#lang racket/base

;; Common functionality used by all space-efficient contracts

(require "prop.rkt"  "blame.rkt")

(provide (struct-out multi-ho/c)
         (struct-out multi-leaf/c)
         build-space-efficient-leaf
         prop:space-efficient-contract
         build-space-efficient-contract-property
         space-efficient-contract?
         merge
         space-efficient-guard
         first-order-check-join
         log-space-efficient-value-bailout-info
         log-space-efficient-contract-bailout-info
          value-safe-for-space-efficient-mode?)

(module+ for-testing
  (provide multi-leaf/c? multi-leaf/c-contract-list multi-leaf/c-proj-list
           get-impersonator-prop:checking-wrapper
           has-impersonator-prop:checking-wrapper?))

;; object contracts need to propagate properties across procedure->method
(module+ properties
  (provide impersonator-prop:checking-wrapper
           has-impersonator-prop:checking-wrapper?
           get-impersonator-prop:checking-wrapper
           impersonator-prop:outer-wrapper-box
           has-impersonator-prop:outer-wrapper-box?
           get-impersonator-prop:outer-wrapper-box
           impersonator-prop:space-efficient
           has-impersonator-prop:space-efficient?
           get-impersonator-prop:space-efficient))

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
;; reference to the outermost chaperone used by the space-efficient contracts
;; needed to detect whether anyone but us is chaperoning values
(define-values (impersonator-prop:outer-wrapper-box
                has-impersonator-prop:outer-wrapper-box?
                get-impersonator-prop:outer-wrapper-box)
  (make-impersonator-property 'impersonator-prop:outer-wrapper-box))
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
  (try-merge
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
         #:space-efficient-guard
         [space-efficient-guard
          (lambda (ctc val)
            (error "internal error: contract does not support `space-efficient-guard`" ctc))]
         #:get-projection
         [get-projection
          (lambda (ctc)
            (lambda (val neg) (error "internal error: contract does not support `get-projection`" ctc)))])
  (space-efficient-contract-property
   (or try-merge (lambda (_1 _2 _3 _4) #f))
   space-efficient-guard
   get-projection))

;; Parent structure for higher order space-efficient contracts
;; which must keep track of the latest blame and missing party
;; and latest contract applied
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
   (lambda (s-e val neg-party)
     (apply-proj-list (multi-leaf/c-proj-list s-e)
                      (multi-leaf/c-missing-party-list s-e)
                      val
                      neg-party))
   #:get-projection
   (lambda (ctc)
     (lambda (val neg-party)
       (error "internal error: tried to apply a leaf as a projection" ctc)))))

(define (build-space-efficient-leaf proj ctc blame)
  (multi-leaf/c (list proj) (list ctc) (list blame) (list #f)))

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
  (define old-blame-pos (or (blame-positive old-blame) old-missing-party old-neg))
  (define old-blame-neg (or (blame-negative old-blame) old-missing-party old-neg))
  (and old-ctc
       (for/or ([new-ctc (in-list new-contract-list)]
                [new-blame (in-list new-blame-list)]
                [new-missing-party (in-list new-missing-party-list)])
         (and new-ctc
              (cond
                [(flat-contract-struct? old-ctc)
                 (contract-struct-stronger? new-ctc old-ctc)]
                [else
                 (define new-blame-pos (or (blame-positive new-blame) new-missing-party new-neg))
                 (define new-blame-neg (or (blame-negative new-blame) new-missing-party new-neg))
                 (and (contract-struct-stronger? new-ctc old-ctc)
                      (contract-struct-stronger? old-ctc new-ctc)
                      (equal? new-blame-pos old-blame-pos)
                      (equal? new-blame-neg old-blame-neg))])))))

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

;; Assuming that merging is symmetric, ie old-can-merge? iff new-can-merge?
;; This is true of the current s-e implementation, but if it ever changes
;; this function will neef to check both directions for merging
(define (merge new-s-e new-neg old-s-e old-neg)
  (define-values (new-try-merge new-proj) (get-merge-components new-s-e))
  (define-values (_ old-proj) (get-merge-components old-s-e))
  (define-values (merged-s-e new-neg) (new-try-merge new-s-e new-neg old-s-e old-neg))
  (cond
    [merged-s-e (values merged-s-e new-neg)]
    [else
     (join-multi-leaf/c (multi->leaf new-s-e new-neg new-proj)
                        new-neg
                        (multi->leaf old-s-e old-neg old-proj)
                        old-neg)]))

(define (get-merge-components multi)
  (define prop (get-space-efficient-contract-property multi))
  (values
   (space-efficient-contract-property-try-merge prop)
   ((space-efficient-contract-property-get-projection prop) multi)))

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
