#lang racket/base

;; Common functionality used by all space-efficient contracts

(require "prop.rkt" "guts.rkt" "blame.rkt")

(provide (struct-out multi/c)
         (struct-out multi-ho/c)
         (struct-out multi-leaf/c)
         convert-to-multi-leaf/c
         apply-proj-list
         implied-by-one?
         join-multi-leaf/c)

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

;; The parent structure of all space-efficient contracts
(struct multi/c ())

;; Parent structure for higher order space-efficient contracts
;; which must keep track of the latest blame and latest contract
;; applied
(struct multi-ho/c multi/c (latest-blame latest-ctc))

(struct multi-leaf/c multi/c (proj-list contract-list))


;; convert a contract into a space-efficient leaf
(define (convert-to-multi-leaf/c ctc blame)
  (multi-leaf/c
   (list ((contract-late-neg-projection ctc) blame))
   (list ctc)))
  

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

;; join two multi-leaf contracts
(define (join-multi-leaf/c old-multi new-multi)
  (define old-proj-list (multi-leaf/c-proj-list old-multi))
  (define old-flat-list (multi-leaf/c-contract-list old-multi))
  (define new-proj-list (multi-leaf/c-proj-list new-multi))
  (define new-flat-list (multi-leaf/c-contract-list new-multi))
  (define-values (not-implied-projs not-implied-flats)
    (for/lists (_1 _2) ([old-proj (in-list old-proj-list)]
                        [old-flat (in-list old-flat-list)]
                        #:when (not (implied-by-one?
                                     new-flat-list old-flat
                                     #:implies contract-stronger?)))
      (values old-proj old-flat)))
  (multi-leaf/c (append new-proj-list not-implied-projs)
                (append new-flat-list not-implied-flats)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; An interface for space-efficient contract conversion and merging
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct space-efficient-contract-property () #:omit-define-syntaxes)

(define (space-efficient-contract-property-guard prop info)
  (unless (space-efficient-contract-property? prop)
    (raise
     (make-exn:fail:contract
      (format "~a: expected a space-efficient contract property; got: ~e"
              prop)
      (current-continuation-marks))))
  prop)

(define-values (prop:space-efficient-contract space-efficient-contract-struct? space-efficient-contract-struct-property)
  (make-struct-type-property 'space-efficient-contract space-efficient-contract-property-guard))


;; merge
;; each thing that can become space-efficient should know how to merge with other space-efficient structures

;; can-merge : a b -> bool
;; true when the contracts of type a and b can be merged
;; for example (multi-)vectorof contracts can merge with (multi-)vectorof contracts, -> and multi-> etc.

;; to-space-efficient : this makes sense for space-efficient structures and regular contracts
;; but it's not clear such a method actually makes sense, because we would only convert when
;; mergin so maybe there isn't a separate conversion ...

;; to-leaf : is the function implemented above for regular contracts,
