#lang racket/base

;; Common functionality used by all space-efficient contracts

(require "prop.rkt"  "blame.rkt")

(provide (struct-out multi-ho/c)
         (struct-out multi-leaf/c)
         build-multi-leaf
         prop:space-efficient-contract
         build-space-efficient-contract-property
         space-efficient-contract?
         ;value-has-space-efficient-support?
         merge
         try-merge
         guard-multi/c
         first-order-check-join
         log-space-efficient-value-bailout-info
         log-space-efficient-contract-bailout-info
         build-s-e-node
         maybe-enter-space-efficient-mode
         impersonator-prop:space-efficient
         has-impersonator-prop:space-efficient?
         get-impersonator-prop:space-efficient
         value-safe-for-space-efficient-mode?)

(module+ for-testing
  (provide multi-leaf/c? multi-leaf/c-contract-list multi-leaf/c-proj-list
           has-impersonator-prop:multi/c? get-impersonator-prop:multi/c
           get-impersonator-prop:checking-wrapper
           has-impersonator-prop:checking-wrapper?))

;; object contracts need to propagate properties across procedure->method
(module+ properties
  (provide impersonator-prop:checking-wrapper
           has-impersonator-prop:checking-wrapper?
           get-impersonator-prop:checking-wrapper
           impersonator-prop:multi/c
           has-impersonator-prop:multi/c?
           get-impersonator-prop:multi/c
           impersonator-prop:outer-wrapper-box
           has-impersonator-prop:outer-wrapper-box?
           get-impersonator-prop:outer-wrapper-box))

(define-logger space-efficient-coerce-contract)
(define-logger space-efficient-value-bailout)
(define-logger space-efficient-contract-bailout)
(define-logger space-efficient-merging)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Data structures

;; reference to the checking wrapper used in space-efficient mode
(define-values (impersonator-prop:checking-wrapper
                has-impersonator-prop:checking-wrapper?
                get-impersonator-prop:checking-wrapper)
  (make-impersonator-property 'impersonator-prop:checking-wrapper))
(define-values (impersonator-prop:multi/c
                has-impersonator-prop:multi/c?
                get-impersonator-prop:multi/c)
  (make-impersonator-property 'impersonator-prop:multi/c))
;; reference to the outermost chaperone used by the space-efficient contracts
;; needed to detect whether anyone but us is chaperoning values
(define-values (impersonator-prop:outer-wrapper-box
                has-impersonator-prop:outer-wrapper-box?
                get-impersonator-prop:outer-wrapper-box)
  (make-impersonator-property 'impersonator-prop:outer-wrapper-box))

;; TODO: maybe this should be the same as multi/c or renamed ... ???
(define-values (impersonator-prop:space-efficient
                has-impersonator-prop:space-efficient?
                get-impersonator-prop:space-efficient)
  (make-impersonator-property 'impersonator-prop:space-efficient))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; An interface for space-efficient contract conversion and merging
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(struct space-efficient-contract-property
  (try-merge-left
   try-merge-right
   value-has-s-e-support?
   space-efficient-guard
   get-projection)
  #:omit-define-syntaxes)

(define (space-efficient-contract-property-guard prop info)
  (unless (space-efficient-contract-property? prop)
    (raise
     (make-exn:fail:contract
      (format "~a: expected a space-efficient contract property; got: ~e"
              prop)
      (current-continuation-marks))))
  prop)

(define-values (prop:space-efficient-contract space-efficient-contract? get-space-efficient-contract-property)
  (make-struct-type-property 'space-efficient-contract space-efficient-contract-property-guard))

(define (build-space-efficient-contract-property
         #:try-merge [try-merge #f]
         #:try-merge-left [try-merge-l #f]
         #:try-merge-right [try-merge-r #f]
         #:value-has-space-efficient-support? [value-has-s-e-support? #f]
         #:space-efficient-guard
         [space-efficient-guard
          (lambda (ctc val)
            (error "internal error: contract does not support `space-efficient-guard`" ctc))]
         #:get-projection
         [get-projection
          (lambda (ctc)
            (lambda (val neg) (error "internal error: contract does not support `get-projection`" ctc)))])
  (unless (or (and try-merge (not try-merge-l) (not try-merge-r))
              (and (not try-merge) (or try-merge-l try-merge-r))
              (and (not try-merge) (not try-merge-l) (not try-merge-r)))
    (error
     'build-space-efficient-contract-property
     (string-append
      "expected either the #:try-merge argument to not be #f or at least one of #:try-merge-left,"
      " #:try-merge-right to not be #f, but not all three")))
  (define try-merge-left
    (or try-merge-l try-merge (lambda (new old) #f)))
  (define try-merge-right
    (or try-merge-r try-merge (lambda (new old) #f)))
  (space-efficient-contract-property
   try-merge-left
   try-merge-right
   (or value-has-s-e-support? (lambda (val) #f))
   space-efficient-guard
   get-projection))

;; Parent structure for higher order space-efficient contracts
;; which must keep track of the latest blame and latest contract
;; applied
(struct multi-ho/c (latest-blame missing-party latest-ctc))

(struct multi-leaf/c (proj-list contract-list blame-list missing-party-list)
  #:property prop:space-efficient-contract
  (build-space-efficient-contract-property
   #:try-merge (lambda (new new-neg old old-neg)
                 (cond
                   [(and (multi-leaf/c? old) (multi-leaf/c? new))
                    (join-multi-leaf/c new new-neg old old-neg)]
                   [else (values #f #f)]))
   #:space-efficient-guard
   (lambda (ctc val) (error "internal error: called space-efficient-guard on a leaf" ctc val))
   #:get-projection
   (lambda (ctc) (lambda (val neg-party) (error "internal error: tried to apply a leaf as a projection" ctc)))))

;; TODO: how to deal with missing blame ???
(define (build-s-e-node s-e proj ctc blame)
  (or s-e
      ;; TODO: need to be sure that ctc is a contract-struct
      (build-multi-leaf proj ctc blame)))

(define (build-multi-leaf proj ctc blame)
  (multi-leaf/c (list proj) (list ctc) (list blame) (list #f)))


;; FIXME: Handle the late-neg passed argument ...
;; Allow the bailout to be passed as an optional to avoid
;; an extra indirection through the property when possible
(define (multi->leaf c neg-party [bail #f])
  (cond
    [(multi-leaf/c? c) c]
    [else
     (define bailout (or bail (get-bail c)))
     (multi-leaf/c
      (list bailout)
      (list #f) ;; Bail out of ctc comparison when we see #f
      (list (multi-ho/c-latest-blame c))
      (list neg-party))]))

;; Apply a list of projections over a value
(define (apply-proj-list proj-list missing-parties val neg-party)
  (for/fold ([val* val])
            ([proj (in-list proj-list)]
             [missing-party (in-list missing-parties)])
    (proj val* (or missing-party neg-party))))

;; checks whether the contract c is already implied by one of the
;; contracts in contract-list
(define (implied-by-one? contract-list c #:implies implies)
  (for/or ([e (in-list contract-list)])
    (implies e c)))

(define (leaf-implied-by-one? new-contract-list new-blame-list new-missing-party-list new-neg
                              old-ctc old-blame old-missing-party old-neg)
  (define old-complete-blame (blame-add-missing-party old-blame (or old-missing-party old-neg)))
  (define old-blame-pos (blame-positive old-complete-blame))
  (define old-blame-neg (blame-negative old-complete-blame))
  (and old-ctc
       (for/or ([new-ctc (in-list new-contract-list)]
                [new-blame (in-list new-blame-list)]
                [new-missing-party (in-list new-missing-party-list)])
         (and new-ctc
              (cond
                [(flat-contract-struct? old-ctc)
                 (contract-struct-stronger? new-ctc old-ctc)]
                [else
                 (define new-complete-blame (blame-add-missing-party new-blame (or new-missing-party new-neg)))
                 (and (contract-struct-stronger? new-ctc old-ctc)
                      (contract-struct-stronger? old-ctc new-ctc)
                      (equal? (blame-positive new-complete-blame) old-blame-pos)
                      (equal? (blame-negative new-complete-blame) old-blame-neg))])))))

;; join two multi-leaf contracts
(define (join-multi-leaf/c old-multi old-neg new-multi new-neg)
  (define old-proj-list (multi-leaf/c-proj-list old-multi))
  (define old-flat-list (multi-leaf/c-contract-list old-multi))
  (define old-blame-list (multi-leaf/c-blame-list old-multi))
  (define old-missing-party-list (multi-leaf/c-missing-party-list old-multi))
  (define new-proj-list (multi-leaf/c-proj-list new-multi))
  (define new-flat-list (multi-leaf/c-contract-list new-multi))
  (define new-blame-list (multi-leaf/c-blame-list new-multi))
  ;; We have to traverse the list to add the new neg party where it is missing
  (define new-missing-party-list (add-missing-parties (multi-leaf/c-missing-party-list new-multi) new-neg))
  (define-values (not-implied-projs not-implied-flats not-implied-blames not-implied-missing-parties)
    (for/lists (_1 _2 _3 _4) ([old-proj (in-list old-proj-list)]
                              [old-flat (in-list old-flat-list)]
                              [old-blame (in-list old-blame-list)]
                              [old-missing-party (in-list old-missing-party-list)]
                              #:when (not (leaf-implied-by-one?
                                           new-flat-list new-blame-list new-missing-party-list new-neg
                                           old-flat old-blame old-missing-party old-neg)))
      (values old-proj old-flat old-blame (or old-missing-party old-neg))))
  (values (multi-leaf/c (fast-append new-proj-list not-implied-projs)
                        (fast-append new-flat-list not-implied-flats)
                        (fast-append new-blame-list not-implied-blames)
                        (fast-append new-missing-party-list not-implied-missing-parties))
          #f))

(define (add-missing-parties missing-parties new-neg-party)
  (for/list ([neg-party (in-list missing-parties)])
    (or neg-party new-neg-party)))


;; A specialized version of append that will immediately return if either
;; argument is empty
(define (fast-append l1 l2)
  (cond
    [(null? l2) l1]
    [(null? l1) l2]
    [else
     (cons (car l1) (fast-append (cdr l1) l2))]))


;; value-has-space-efficient-support? : space-efficient? any/c -> boolean?
;; Returns #t if the value can be guarded with this s-e contract
(define (value-has-space-efficient-support? s-e val)
  (and (space-efficient-contract? s-e)
       (let* ([prop (get-space-efficient-contract-property s-e)]
              [has-space-efficient-support?
               (space-efficient-contract-property-value-has-s-e-support? prop)])
         (has-space-efficient-support? val))))

;; Assuming that merging is symmetric, ie old-can-merge? iff new-can-merge?
;; This is true of the current s-e implementation, but if it ever changes
;; this function will neef to check both directions for merging
(define ((make-merge build-leaf?) new-multi new-neg old-multi old-neg)
  (cond
    ;; NOTE: is it safe to just use the new-neg blame if the contract structures are the same?
    [(eq? new-multi old-multi)
     (log-space-efficient-merging-info (format "eq?-neg-blame: ~s" (eq? new-neg old-neg)))
     (values new-multi new-neg)]
    [else
     (log-space-efficient-merging-info "distinct contracts")
     (define-values (new-try-merge-left _1 new-proj) (get-merge-components new-multi))
     (define-values (_2 old-try-merge-right old-proj) (get-merge-components old-multi))
     (define-values (left-merge left-neg) (new-try-merge-left new-multi new-neg old-multi old-neg))
     (cond
       [left-merge (values left-merge left-neg)]
       [else
        (define-values (right-merge right-neg) (old-try-merge-right new-multi new-neg old-multi old-neg))
        (cond
          [right-merge (values right-merge right-neg)]
          [build-leaf?
           (join-multi-leaf/c (multi->leaf new-multi new-neg new-proj)
                              new-neg
                              (multi->leaf old-multi old-neg old-proj)
                              old-neg)]
          [else (values #f #f)])])]))

(define merge (make-merge #t))
(define try-merge (make-merge #f))

(define (get-merge-components multi)
  (cond
    [(space-efficient-contract? multi)
     (define prop (get-space-efficient-contract-property multi))
     (values
      (space-efficient-contract-property-try-merge-left prop)
      (space-efficient-contract-property-try-merge-right prop)
      ((space-efficient-contract-property-get-projection prop) multi))]
    [else
     (values merge-fail merge-fail #f)]))

;; TODO: should this return one of the blames as the second return value?
(define (merge-fail _1 _2 _3 _4) (values #f #f))

(define (guard-multi/c multi val neg-party)
  (unless (space-efficient-contract? multi)
    (error "internal error: not a space-efficient contract" multi))
  (cond
    [(multi-leaf/c? multi)
     ;; make the leaf case generic
     (apply-proj-list (multi-leaf/c-proj-list multi)
                      (multi-leaf/c-missing-party-list multi)
                      val
                      neg-party)]
    [else
     (space-efficient-guard multi val neg-party)]))

(define (space-efficient-guard multi val neg-party)
  (define prop (get-space-efficient-contract-property multi))
  (define guard (space-efficient-contract-property-space-efficient-guard prop))
  (guard multi val neg-party))

(define (get-bail multi)
  (define prop (space-efficient-contract-property multi))
  ((space-efficient-contract-property-get-projection prop) multi))

(define (first-order-check-join new-checks old-checks stronger?)
  (fast-append new-checks
          (for/list ([old (in-list old-checks)]
                     #:when (not (implied-by-one?
                                  new-checks old
                                  #:implies stronger?)))
            old)))

;; TODO: remove this
(define (maybe-enter-space-efficient-mode s-e val neg-party)
  (and (has-impersonator-prop:space-efficient? val)
       ;; try deleting this
       (get-impersonator-prop:space-efficient val)
       (value-has-space-efficient-support? s-e val)
       (guard-multi/c s-e val neg-party)))

(define (value-safe-for-space-efficient-mode? val chap-not-imp?)
  (define-syntax-rule (bail reason)
    (begin
      (log-space-efficient-value-bailout-info (format "not-space-efficient: ~a" reason))
      #f))
  (and
   ;; we also can't use this optimization on a value that has been
   ;; chaperoned by a 3rd party since it's been contracted
   ;; (because this optimization relies on replacing wrappers, which
   ;; would drop this 3rd-party chaperone)
   (or (if (has-impersonator-prop:outer-wrapper-box? val)
           (eq? val (unbox (get-impersonator-prop:outer-wrapper-box val)))
           #t)
       (bail "has been chaperoned since last contracted"))
   ;; can't switch from chaperone wrappers to impersonator wrappers, and
   ;; vice versa. if we would bail out of the optimization
   (or (cond
         [(has-impersonator-prop:checking-wrapper? val)
          (define checking-wrapper
            (get-impersonator-prop:checking-wrapper val))
          (equal? (chaperone? checking-wrapper)
                  chap-not-imp?)]
         [else #t])
       (bail "switching from imp to chap or vice versa"))))
