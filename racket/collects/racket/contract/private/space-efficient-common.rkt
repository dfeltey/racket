#lang racket/base

;; Common functionality used by all space-efficient contracts

(require "prop.rkt" "guts.rkt" "blame.rkt")

(provide (struct-out multi/c)
         (struct-out multi-ho/c)
         (struct-out multi-leaf/c)
         (struct-out first-order-check)
         convert-to-multi-leaf/c
         apply-proj-list
         prop:space-efficient-support
         prop:space-efficient-contract
         contract-has-space-efficient-support?
         contract->space-efficient-contract
         build-space-efficient-support-property
         build-space-efficient-contract-property
         space-efficient-contract?
         merge
         guard-multi/c
         first-order-check-join
         enter-space-efficient-mode)

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
(struct space-efficient-support-property
  (has-space-efficient-support?
   convert)
  #:omit-define-syntaxes)

(define (space-efficient-support-property-guard prop info)
  (unless (space-efficient-support-property? prop)
    (raise
     (make-exn:fail:contract
      (format "~a: expected a space-efficient-support property; got ~e"
              prop)
      (current-continuation-marks))))
  prop)

(define-values (prop:space-efficient-support struct-has-space-efficient-support? space-efficient-support-struct-property)
  (make-struct-type-property 'space-efficient-support space-efficient-support-property-guard))

(define (build-space-efficient-support-property
         #:has-space-efficient-support? has-space-efficient-support?
         #:convert convert)
  (space-efficient-support-property has-space-efficient-support? convert))

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
         #:try-merge try-merge
         #:space-efficient-guard space-efficient-guard
         #:get-projection get-projection)
  (space-efficient-contract-property
   try-merge
   space-efficient-guard
   get-projection))

(struct multi/c ()
  #:property prop:space-efficient-support
  (build-space-efficient-support-property
   #:has-space-efficient-support? (lambda (ctc) #t)
   #:convert (lambda (ctc blame) ctc)))

;; Parent structure for higher order space-efficient contracts
;; which must keep track of the latest blame and latest contract
;; applied
(struct multi-ho/c multi/c (latest-blame latest-ctc))

(struct multi-leaf/c multi/c (proj-list contract-list blame-list)
  #:property prop:space-efficient-contract
  (build-space-efficient-contract-property
   #:try-merge (lambda (new old) (and (multi-leaf/c? new) (join-multi-leaf/c new old)))
   #:space-efficient-guard
   (lambda (ctc val) (error "internal error: called space-efficient-guard on a leaf" ctc val))
   #:get-projection
   (lambda (ctc) (lambda (val neg-party) (error "internal error: tried to apply a leaf as a projection" ctc)))))

;; Parent structure for first-order checks
(struct first-order-check ())

;; convert a contract into a space-efficient leaf
(define (convert-to-multi-leaf/c ctc blame)
  (multi-leaf/c
   (list ((contract-late-neg-projection ctc) blame))
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
      (list (gensym)) ;; need to be incomparable via contract-stronger?
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

(define (leaf-implied-by-one? new-contract-list new-blame-list old-ctc old-blame #:implies implies)
  (define old-blame-pos (blame-positive old-blame))
  (define old-blame-neg (blame-negative old-blame))
  (for/or ([new-ctc (in-list new-contract-list)]
           [new-blame (in-list new-blame-list)])
    (if (flat-contract? old-ctc)
        (implies new-ctc old-ctc)
        (and (implies new-ctc old-ctc)
             (implies old-ctc new-ctc)
             (equal? (blame-positive new-blame) old-blame-pos)
             (equal? (blame-negative new-blame) old-blame-neg)))))

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
                                        old-flat old-blame
                                        #:implies contract-stronger?)))
      (values old-proj old-flat old-blame)))
  (multi-leaf/c (append new-proj-list not-implied-projs)
                (append new-flat-list not-implied-flats)
                (append new-blame-list not-implied-blames)))

;; contract-has-space-efficient-support? : any/c -> boolean?
;; Returns #t if the value is a contract with space-efficient support
(define (contract-has-space-efficient-support? ctc)
  (or (multi/c? ctc) ; already a space-efficient contract
      ;; maybe this check needs to be a multi-ho/c because if we have a leaf something else should happen
      (and (struct-has-space-efficient-support? ctc)
           (let* ([prop (space-efficient-support-struct-property ctc)]
                  [has-space-efficient-support?
                   (space-efficient-support-property-has-space-efficient-support? prop)])
             (has-space-efficient-support? ctc)))))

;; contract->space-efficient-contract : contract? blame? boolean? -> multi/c?
;; converts a contract into a space-efficient contract, if the contract
;; has space-efficient support, we dispatch to it's convert property
;; otherwise we build a multi-leaf/c
(define (contract->space-efficient-contract ctc blame)
  (cond
    [(struct-has-space-efficient-support? ctc)
     (define prop (space-efficient-support-struct-property ctc))
     (define convert (space-efficient-support-property-convert prop))
     (convert ctc blame)]
    [else
     (convert-to-multi-leaf/c ctc blame)]))

;; Assuming that merging is symmetric, ie old-can-merge? iff new-can-merge?
;; This is true of the current s-e implementation, but if it ever changes
;; this function will neef to check both directions for merging
(define (merge new-multi old-multi)
  (define-values (_ new-proj) (get-merge-components new-multi))
  (define-values (old-try-merge old-proj) (get-merge-components old-multi))
  (or (old-try-merge new-multi old-multi)
      (join-multi-leaf/c (multi->leaf new-multi new-proj)
                         (multi->leaf old-multi old-proj))))

(define (get-merge-components multi)
  (cond
    [(space-efficient-contract? multi)
     (define prop (get-space-efficient-contract-property multi))
     (values
      (space-efficient-contract-property-try-merge prop)
      ((space-efficient-contract-property-get-projection prop) multi))]
    [else
     (values merge-fail #f)]))
      
(define (merge-fail _1 _2) #f)

(define (guard-multi/c multi val)
  (cond
    [(multi-leaf/c? multi)
     (apply-proj-list (multi-leaf/c-proj-list multi) val)]
    [else
     (unless (space-efficient-contract? multi)
       (error "internal error: not a space-efficient contract" multi))
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

