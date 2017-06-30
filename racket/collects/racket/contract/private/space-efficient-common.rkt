#lang racket/base

;; Common functionality used by all space-efficient contracts

(require "prop.rkt" "guts.rkt" "blame.rkt")

(provide (struct-out multi/c)
         (struct-out multi-ho/c)
         (struct-out multi-leaf/c)
         (struct-out first-order-check)
         convert-to-multi-leaf/c
         apply-proj-list
         implied-by-one?
         join-multi-leaf/c
         multi->leaf
         prop:space-efficient-support
         contract-has-space-efficient-support?
         contract->space-efficient-contract
         build-space-efficient-support-property)

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

;; TODO: can possibly move the space-efficient support property here
;;       rather than the child structs
;; The parent structure of all space-efficient contracts
(struct multi/c ())

;; Parent structure for higher order space-efficient contracts
;; which must keep track of the latest blame and latest contract
;; applied
(struct multi-ho/c multi/c (latest-blame latest-ctc))

(struct multi-leaf/c multi/c (proj-list contract-list blame-list))

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
(define (multi->leaf c chap-not-imp? [bail #f])
  (cond
    [(multi-leaf/c? c) c]
    [else
     (define bailout (or bail (get-bail c)))
     (multi-leaf/c
      (list (lambda (val neg-party) (bailout c val chap-not-imp?)))
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
(define (contract->space-efficient-contract ctc blame chap-not-imp?)
  (cond
    [(struct-has-space-efficient-support? ctc)
     (define prop (space-efficient-support-struct-property ctc))
     (define convert (space-efficient-support-property-convert prop))
     (convert ctc blame chap-not-imp?)]
    [else
     (convert-to-multi-leaf/c ctc blame)]))

(struct space-efficient-contract-property
  (can-merge?
   construct
   first-order-checks
   positive-subcontracts
   negative-subcontracts
   bail-to-regular-wrapper
   first-order-stronger?
   guard-multi
   do-first-order-checks
   value-has-s-e-support?)
  #:omit-define-syntaxes)

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

;; Assuming that merging is symmetric, ie old-can-merge? iff new-can-merge?
;; This is true of the current s-e implementation, but if it ever changes
;; this function will neef to check both directions for merging
(define (merge new-multi old-multi chap-not-imp?)
  (cond
    [(and (multi-ho/c? new-multi) (multi-ho/c? old-multi))
     (define-values (new-can-merge? new-construct new-first-order new-pos new-neg new-bail new-fo-stronger?)
       (get-merge-components new-multi))
     (define-values (old-can-merge? old-construct old-first-order old-pos old-neg old-bail old-fo-stronger?)
       (get-merge-components old-multi))
     (cond
       [(old-can-merge? new-multi old-multi chap-not-imp?)
        (old-construct
         (multi-ho/c-latest-blame new-multi)
         (multi-ho/c-latest-ctc new-multi)
         (first-order-check-join old-first-order new-first-order old-fo-stronger?)
         (merge* new-pos old-pos chap-not-imp?)
         (merge* old-neg new-neg chap-not-imp?))]
       [else
        (join-multi-leaf/c (multi->leaf new-multi chap-not-imp? new-bail)
                           (multi->leaf old-multi chap-not-imp? old-bail))])]
    [else
     (join-multi-leaf/c (multi->leaf new-multi chap-not-imp?)
                        (multi->leaf old-multi chap-not-imp?))]))

(define (merge* new old chap-not-imp?)
  (cond
    [(and (multi/c? new) (multi/c? old))
     (merge new old chap-not-imp?)]
    [(and (vector? new) (vector? old))
     (for/vector ([nc (in-vector new)]
                  [oc (in-vector old)])
       (merge nc oc chap-not-imp?))]
    [(vector? new)
     (for/vector ([nc (in-vector new)])
       (merge nc old chap-not-imp?))]
    [(vector? old)
     (for/vector ([oc (in-vector old)])
       (merge new oc chap-not-imp?))]
    [else
     (error "internal error: unexpected combination of space-efficient contracts" new old)]))


;; NOTE: All the higher-order s-e contracts have positive/negative/first-order components
;; these could be stored in the multi-ho/c struct so that we don't need to look up so
;; many things on the property itself, then the individual structs only need to support
;; can-merge?/construct/bail/first-order-stronger/guard etc ...
;; This makes it harder for others to extend the s-e contracts though
(define (get-merge-components multi)
  (define prop (space-efficient-contract-struct-property multi))
  (values (space-efficient-contract-property-can-merge? prop)
          (space-efficient-contract-property-construct prop)
          (space-efficient-contract-property-first-order-checks prop)
          (space-efficient-contract-property-positive-subcontracts prop)
          (space-efficient-contract-property-negative-subcontracts prop)
          (space-efficient-contract-property-bail-to-regular-wrapper prop)
          (space-efficient-contract-property-first-order-stronger? prop)))

(define (get-bail . args) (error "TODO"))
;; might need this for guard-multi
(define (bail . args) (error "TODO"))


(define (first-order-check-join new-checks old-checks stronger?)
  (append new-checks
          (for/list ([old (in-list old-checks)]
                     #:when (not (implied-by-one?
                                  new-checks old
                                  #:implies stronger?)))
            old)))
