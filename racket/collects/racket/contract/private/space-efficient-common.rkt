#lang racket/base

;; Common functionality used by all space-efficient contracts

(require "prop.rkt" "guts.rkt" "blame.rkt")

(provide (struct-out multi-ho/c)
         (struct-out multi-leaf/c)
         apply-proj-list
         prop:space-efficient-contract
         contract-has-space-efficient-support?
         contract->space-efficient-contract
         build-space-efficient-contract-property
         space-efficient-contract?
         merge
         guard-multi/c
         first-order-check-join
         enter-space-efficient-mode
         log-space-efficient-value-bailout-info
         log-space-efficient-contract-bailout-info)

(module+ for-testing
  (provide multi-leaf/c? multi-leaf/c-contract-list multi-leaf/c-proj-list
           has-impersonator-prop:multi/c? get-impersonator-prop:multi/c
           get-impersonator-prop:checking-wrapper))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; An interface for space-efficient contract conversion and merging
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(struct space-efficient-contract-property
  (has-space-efficient-support?
   convert
   try-merge-left
   try-merge-right
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
         #:has-space-efficient-support? [has-space-efficient-support? (lambda (_) #t)]
         #:convert [convert (lambda (ctc blame) ctc)]
         #:try-merge [try-merge #f]
         #:try-merge-left [try-merge-l #f]
         #:try-merge-right [try-merge-r #f]
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
   has-space-efficient-support?
   convert
   try-merge-left
   try-merge-right
   space-efficient-guard
   get-projection))

;; Parent structure for higher order space-efficient contracts
;; which must keep track of the latest blame and latest contract
;; applied
(struct multi-ho/c (latest-blame latest-ctc))

(struct multi-leaf/c (proj-list contract-list blame-list)
  #:property prop:space-efficient-contract
  (build-space-efficient-contract-property
   #:try-merge (lambda (new old) (and (multi-leaf/c? old) (multi-leaf/c? new) (join-multi-leaf/c new old)))
   #:space-efficient-guard
   (lambda (ctc val) (error "internal error: called space-efficient-guard on a leaf" ctc val))
   #:get-projection
   (lambda (ctc) (lambda (val neg-party) (error "internal error: tried to apply a leaf as a projection" ctc)))))

;; convert a contract into a space-efficient leaf
(define (convert-to-multi-leaf/c ctc blame)
  (define cctc
    (cond
      [(contract-struct? ctc) ctc]
      [else
       (log-space-efficient-coerce-contract-info (format "~s" ctc))
       (coerce-contract/f ctc)]))
  (multi-leaf/c
   (list ((get/build-late-neg-projection cctc) blame))
   (list ctc)
   (list blame)))

;; Allow the bailout to be passed as an optional to avoid
;; an extra indirection through the property when possible
(define (multi->leaf c [bail #f])
  (cond
    [(multi-leaf/c? c) c]
    [else
     (define bailout (or bail (get-bail c)))
     (multi-leaf/c
      (list bailout)
      (list #f) ;; Bail out of ctc comparison when we see #f
      (list (multi-ho/c-latest-blame c)))]))

;; Apply a list of projections over a value
;; Note that for our purposes it is important to fold left otherwise blame
;; could be assigned in the wrong order
;; [a -> (Maybe a)] -> a -> (Maybe a)
(define (apply-proj-list proj-list val)
  (for/fold ([val* val])
            ([proj (in-list proj-list)])
    (proj val* #f))) ; #f neg-party (already in blame)

;; checks whether the contract c is already implied by one of the
;; contracts in contract-list
(define (implied-by-one? contract-list c #:implies implies)
  (for/or ([e (in-list contract-list)])
    (implies e c)))

(define (leaf-implied-by-one? new-contract-list new-blame-list old-ctc old-blame)
  (define old-blame-pos (blame-positive old-blame))
  (define old-blame-neg (blame-negative old-blame))
  (and old-ctc
       (for/or ([new-ctc (in-list new-contract-list)]
                [new-blame (in-list new-blame-list)])
         (and new-ctc
              (if (flat-contract? old-ctc)
                  (contract-struct-stronger? new-ctc old-ctc)
                  (and (contract-struct-stronger? new-ctc old-ctc)
                       (contract-struct-stronger? old-ctc new-ctc)
                       (equal? (blame-positive new-blame) old-blame-pos)
                       (equal? (blame-negative new-blame) old-blame-neg)))))))

;; join two multi-leaf contracts
(define (join-multi-leaf/c old-multi new-multi)
  (define old-proj-list (multi-leaf/c-proj-list old-multi))
  (define old-flat-list (multi-leaf/c-contract-list old-multi))
  (define old-blame-list (multi-leaf/c-blame-list old-multi))
  (define new-proj-list (multi-leaf/c-proj-list new-multi))
  (define new-flat-list (multi-leaf/c-contract-list new-multi))
  (define new-blame-list (multi-leaf/c-blame-list new-multi))
  (define-values (not-implied-projs not-implied-flats not-implied-blames)
    (for/lists (_1 _2 _3) ([old-proj (in-list old-proj-list)]
                           [old-flat (in-list old-flat-list)]
                           [old-blame (in-list old-blame-list)]
                           #:when (not (leaf-implied-by-one?
                                        new-flat-list new-blame-list
                                        old-flat old-blame)))
      (values old-proj old-flat old-blame)))
  (multi-leaf/c (append new-proj-list not-implied-projs)
                (append new-flat-list not-implied-flats)
                (append new-blame-list not-implied-blames)))

;; contract-has-space-efficient-support? : any/c -> boolean?
;; Returns #t if the value is a contract with space-efficient support
(define (contract-has-space-efficient-support? ctc)
  (and (space-efficient-contract? ctc)
       (let* ([prop (get-space-efficient-contract-property ctc)]
              [has-space-efficient-support?
               (space-efficient-contract-property-has-space-efficient-support? prop)])
         (has-space-efficient-support? ctc))))

;; contract->space-efficient-contract : contract? blame? boolean? -> multi/c?
;; converts a contract into a space-efficient contract, if the contract
;; has space-efficient support, we dispatch to it's convert property
;; otherwise we build a multi-leaf/c
(define (contract->space-efficient-contract ctc blame)
  (cond
    [(space-efficient-contract? ctc)
     (define prop (get-space-efficient-contract-property ctc))
     (define has-support? (space-efficient-contract-property-has-space-efficient-support? prop))
     (define convert (space-efficient-contract-property-convert prop))
     (if (has-support? ctc)
         (convert ctc blame)
         (convert-to-multi-leaf/c ctc blame))]
    [else
     (convert-to-multi-leaf/c ctc blame)]))

;; Assuming that merging is symmetric, ie old-can-merge? iff new-can-merge?
;; This is true of the current s-e implementation, but if it ever changes
;; this function will neef to check both directions for merging
(define (merge new-multi old-multi)
  (define-values (new-try-merge-left _1 new-proj) (get-merge-components new-multi))
  (define-values (_2 old-try-merge-right old-proj) (get-merge-components old-multi))
  (or (new-try-merge-left new-multi old-multi)
      (old-try-merge-right new-multi old-multi) 
      (join-multi-leaf/c (multi->leaf new-multi new-proj)
                         (multi->leaf old-multi old-proj))))

(define (get-merge-components multi)
  (cond
    [(space-efficient-contract? multi)
     (define prop (get-space-efficient-contract-property multi))
     (values
      (space-efficient-contract-property-try-merge-left prop)
      (space-efficient-contract-property-try-merge-right prop)
      ((space-efficient-contract-property-get-projection prop) multi))]
    [else
     (values merge-fail #f)]))
      
(define (merge-fail _1 _2) #f)

(define (guard-multi/c multi val)
  (unless (space-efficient-contract? multi)
    (error "internal error: not a space-efficient contract" multi))
  (cond
    [(multi-leaf/c? multi)
     (apply-proj-list (multi-leaf/c-proj-list multi) val)]
    [else
     (space-efficient-guard multi val)]))

(define (space-efficient-guard multi val)
  (define prop (get-space-efficient-contract-property multi))
  (define guard (space-efficient-contract-property-space-efficient-guard prop))
  (guard multi val))

(define (get-bail multi)
  (define prop (space-efficient-contract-property multi))
  ((space-efficient-contract-property-get-projection prop) multi))

(define (first-order-check-join new-checks old-checks stronger?)
  (append new-checks
          (for/list ([old (in-list old-checks)]
                     #:when (not (implied-by-one?
                                  new-checks old
                                  #:implies stronger?)))
            old)))

(define (enter-space-efficient-mode val ctc blame)
  (and (has-contract? val)
       (contract-has-space-efficient-support? ctc)
       (contract-has-space-efficient-support? (value-contract val))
       (guard-multi/c (contract->space-efficient-contract ctc blame)
                      val)))

