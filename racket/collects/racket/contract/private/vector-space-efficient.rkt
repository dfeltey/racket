#lang racket/base

(require "prop.rkt" "guts.rkt" "blame.rkt" (only-in racket/unsafe/ops unsafe-chaperone-vector unsafe-impersonate-vector)
         (submod "arrow-space-efficient.rkt" properties))

;; TODO:
;; - first order checks
;; - vector/c space efficient
;; - chaperone/impersonator dance
;; - checking values/contracts for space-efficient support
;;   - values: already chaperoned/impersonated won't work
;;   - chaperones on top of space-efficient wrappers won't work
;;   - compare w/ functions
;;   - contracts: various vectorof? flags

(provide (struct-out base-vectorof)
         space-efficient-guard
         value-has-space-efficient-support?
         do-check-vectorof)

(module+ for-testing
  (provide multi/c? multi-vectorof? multi-vectorof-ref-ctc multi-vectorof-set-ctc
           multi-leaf/c? multi-leaf/c-proj-list multi-leaf/c-contract-list
           value-has-space-efficient-support?))


(define debug-bailouts #f)

;; TODO: This isn't the right place for vectorof, but it will get things working
;; eager is one of:
;; - #t: always perform an eager check of the elements of an immutable vector
;; - #f: never  perform an eager check of the elements of an immutable vector
;; - N (for N>=0): perform an eager check of immutable vectors size <= N
(define-struct base-vectorof (elem immutable eager))

(struct multi/c ())
(struct first-order-check (immutable blame)) ;; TODO: handle immutability ...

;; TODO: transparent only for debugging
(struct multi-vectorof multi/c (ref-ctc set-ctc first-order latest-blame) #:transparent)
(struct chaperone-multi-vectorof multi-vectorof () #:transparent)
(struct multi-leaf/c multi/c (proj-list contract-list) #:transparent)


;; abstracted from the former check-vectorof implementation in
;; the vector contract implementation, this is the common piece
;; that is needed for the space-efficient machinery to perform first-order checks
(define (do-check-vectorof val fail immutable)
  (unless (vector? val)
    (fail val '(expected "a vector," given: "~e") val))
  (cond
    [(eq? immutable #t)
     (unless (immutable? val)
       (fail val '(expected "an immutable vector" given: "~e") val))]
    [(eq? immutable #f)
     (when (immutable? val)
       (fail val '(expected "an mutable vector" given: "~e") val))]
    [else (void)]))


(define (do-first-order-checks m/c val)
  (define checks (multi-vectorof-first-order m/c))
  (for ([c (in-list checks)])
    (define immutable (first-order-check-immutable c))
    (define blame (first-order-check-blame c))
    (define (raise-blame val . args)
      (apply raise-blame-error blame #:missing-party #f val args))
    (do-check-vectorof val raise-blame immutable)))

;; stub
(define (contract-has-space-efficient-support? ctc) #t)

(define (value-has-space-efficient-support? val ctc)
  (define (bail reason)
    (when debug-bailouts
      (printf "value bailing: ~a -- ~a\n" reason val))
    #f)
  (and (or (vector? val)
           (bail "not a vector"))
       (or (if (has-impersonator-prop:unwrapped? val)
               (not (impersonator? (get-impersonator-prop:unwrapped val)))
               #t)
           (bail "already chaperoned"))
       (or (if (has-impersonator-prop:outer-wrapper-box? val)
               (eq? val (unbox (get-impersonator-prop:outer-wrapper-box val)))
               #t)
           (bail "has been chaperoned since last contracted"))
       ;;TODO: handle disallowing switching between chaperone and impersonator wrappers
       ))

(define (first-order-check-stronger? f1 f2)
  #f
  #;(contract-stronger? (first-order-check-ctc f1)
                      (first-order-check-ctc f2)))


(define (vectorof->multi-vectorof ctc blame)
  (cond
    [(multi-vectorof? ctc) ; already space efficient
     ctc]
    [(and (base-vectorof? ctc) (contract-has-space-efficient-support? ctc))
     (define elem (base-vectorof-elem ctc))
     (define set-blame (blame-swap blame))
     (chaperone-multi-vectorof
      (vectorof->multi-vectorof elem blame)
      (vectorof->multi-vectorof elem set-blame)
      (list (first-order-check (base-vectorof-immutable ctc) blame))
      blame)]
    [else ; convert to a leaf
     (multi-leaf/c
      (list ((contract-late-neg-projection ctc) blame))
      (list ctc))]))

;; checks whether the contract c is already implied by one of the
;; contracts in contract-list
(define (implied-by-one? contract-list c #:implies implies)
  (for/or ([e (in-list contract-list)])
    (implies e c)))

;; join two multi-leaf contracts
(define (multi-leaf/c-join old-multi new-multi)
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

(define (first-order-check-join new-checks old-checks)
  (append new-checks
          (for/list ([old (in-list old-checks)]
                     #:when (not (implied-by-one?
                                  new-checks old
                                  #:implies first-order-check-stronger?)))
            old)))

(define (join-multi-vectorof new-multi old-multi)
  (define (multi->leaf c)
    (multi-leaf/c
     ;; create a regular projection from the multi wrapper
     (list (λ (val neg-party)
             (bail-to-regular-wrapper c val
                                      (or (chaperone-multi-vectorof? old-multi)
                                          (chaperone-multi-vectorof? new-multi)))))
     ;; incomparable value for `contract-stronger?`
     (list (gensym))))
  (cond
    [(and (multi-vectorof? old-multi) (multi-vectorof? new-multi))
     (chaperone-multi-vectorof
      (join-multi-vectorof (multi-vectorof-ref-ctc new-multi)
                           (multi-vectorof-ref-ctc old-multi))
      (join-multi-vectorof (multi-vectorof-set-ctc old-multi)
                           (multi-vectorof-set-ctc new-multi))
      (first-order-check-join (multi-vectorof-first-order old-multi)
                              (multi-vectorof-first-order new-multi))
      (multi-vectorof-latest-blame new-multi))]
    [(multi-vectorof? old-multi)
     (multi-leaf/c-join new-multi (multi->leaf old-multi))]
    [(multi-vectorof? new-multi)
     (multi-leaf/c-join (multi->leaf new-multi) old-multi)]
    [else
     (multi-leaf/c-join new-multi old-multi)]))

;; TODO: impersonator property
;; TODO: hand chaperones and impersonators
(define (space-efficient-guard ctc val blame)
  (define (make-checking-wrapper unwrapped)
    (chaperone-vector* unwrapped chaperone-ref-wrapper chaperone-set-wrapper))
  (define-values (merged-ctc checking-wrapper)
    (cond [(has-impersonator-prop:multi/c? val)
           (unless (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting a checking wrapper" val))
           (values (join-multi-vectorof (vectorof->multi-vectorof ctc blame)
                                        (get-impersonator-prop:multi/c val))
                   (get-impersonator-prop:checking-wrapper val))]
          [(has-contract? val)
           (when (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting no checking wrapper" val))
           (define orig-ctc (value-contract val))
           (define orig-blame (value-blame val))
           (define unwrapped ;; un-contracted (since it is wrapped in a chaperone)
             (unsafe-chaperone-vector
              val
              (get-impersonator-prop:unwrapped val)))
           (values (join-multi-vectorof
                    (vectorof->multi-vectorof ctc blame)
                    (vectorof->multi-vectorof orig-ctc orig-blame))
                   (make-checking-wrapper unwrapped))]
          [else
           (unless (multi-vectorof? ctc)
             (error "internal error: expecting a space-efficient contract" ctc))
           (when (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting no checking wrapper" val))
           (values ctc (make-checking-wrapper val))]))
  ;; Need to pass the unwrapped val here, otherwise contract checking will loop
  ;; These checks are also duplicated in the contract system, so it's unclear
  ;; what should happen to them
  ;; moving these to guard-multi
  ; (do-first-order-checks merged-ctc val #;checking-wrapper)
  (define b (box #f))
  (define res
    (chaperone-vector
     checking-wrapper
     #f
     #f
     impersonator-prop:checking-wrapper checking-wrapper
     impersonator-prop:outer-wrapper-box b
     impersonator-prop:multi/c merged-ctc
     ;; TODO: impersonator-prop:contracted 
     impersonator-prop:blame (multi-vectorof-latest-blame merged-ctc)))
  (set-box! b res)
  res)

;; Apply a list of projections over a value
;; Note that for our purposes it is important to fold left otherwise blame
;; could be assigned in the wrong order
;; [a -> (Maybe a)] -> a -> (Maybe a)
(define (apply-proj-list proj-list val)
  (foldl (lambda (f v) (f v #f)) val proj-list)) ; #f neg-party (already in blame)

;; TODO: first order checks
(define (guard-multi/c ctc val)
  (unless (multi/c? ctc)
    (error "internal error: not a space-efficient contract"))
  (cond
    [(multi-leaf/c? ctc)
     (apply-proj-list (multi-leaf/c-proj-list ctc) val)]
    [(value-has-space-efficient-support? val ctc)
     (do-first-order-checks ctc val)
     (space-efficient-guard ctc val (multi-vectorof-latest-blame ctc))]
    [else
     (bail-to-regular-wrapper ctc val #f)]))

;; TODO: first order checks????
(define (chaperone-ref-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define ref-ctc (multi-vectorof-ref-ctc ctc))
  (guard-multi/c ref-ctc elt))
  
(define (chaperone-set-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define set-ctc (multi-vectorof-set-ctc ctc))
  (guard-multi/c set-ctc elt))

(define (bail-to-regular-wrapper m/c val chap-not-imp?)
  (do-first-order-checks m/c val)
  (chaperone-vector*
   val
   chaperone-ref-wrapper
   chaperone-set-wrapper
   ;; TODO: impersonator-prop:contracted, don't currently keep track of
   ;;       the latest contract ...
   ;; TODO: not sure if this is always going to be the correct blame right now???
   impersonator-prop:blame (multi-vectorof-latest-blame m/c)))
