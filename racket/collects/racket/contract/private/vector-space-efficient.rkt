#lang racket/base

(require "prop.rkt" "guts.rkt" "blame.rkt" (only-in racket/unsafe/ops unsafe-chaperone-vector unsafe-impersonate-vector)
         (submod "arrow-space-efficient.rkt" properties))

;; TODO:
;; DONE: first order checks
;; MOSTLY DONE vector/c space efficient
;; DONE: chaperone/impersonator dance
;; - checking values/contracts for space-efficient support
;;   DONE: values: already chaperoned/impersonated won't work
;;   DONE: chaperones on top of space-efficient wrappers won't work
;;   DONE: compare w/ functions
;;   - contracts: various vectorof? flags
;; - Refactor the space efficient contract implementation and vector contracts

(provide (struct-out base-vectorof)
         vectorof-space-efficient-guard
         value-has-vectorof-space-efficient-support?
         do-check-vectorof)

(module+ for-testing
  (provide multi/c? multi-vectorof? multi-vectorof-ref-ctc multi-vectorof-set-ctc
           multi-leaf/c? multi-leaf/c-proj-list multi-leaf/c-contract-list
           value-has-vectorof-space-efficient-support?))

(define debug-bailouts #f)

;; TODO: This isn't the right place for vectorof, but it will get things working
;; eager is one of:
;; - #t: always perform an eager check of the elements of an immutable vector
;; - #f: never  perform an eager check of the elements of an immutable vector
;; - N (for N>=0): perform an eager check of immutable vectors size <= N
(define-struct base-vectorof (elem immutable eager))

(struct multi/c ())
(struct first-order-check (immutable blame))

(struct multi-vectorof multi/c (ref-ctc set-ctc first-order latest-blame latest-ctc))
(struct chaperone-multi-vectorof multi-vectorof ())
(struct impersonator-multi-vectorof multi-vectorof ())
(struct multi-leaf/c multi/c (proj-list contract-list))


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

(define (value-has-vectorof-space-efficient-support? val chap-not-imp?)
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
       ;; disallow switching between chaperone and impersonator wrappers
       (or (cond [(has-impersonator-prop:checking-wrapper? val)
                  (define checking-wrapper
                    (get-impersonator-prop:checking-wrapper val))
                  (if (chaperone? checking-wrapper)
                      chap-not-imp?
                      (not chap-not-imp?))]
                 [else
                  (if chap-not-imp?
                      (chaperone-contract?    (value-contract val))
                      (impersonator-contract? (value-contract val)))])
           (bail "switching from imp to chap or vice versa"))))

(define (first-order-check-stronger? f1 f2)
  (define f1-immutable (first-order-check-immutable f1))
  (define f2-immutable (first-order-check-immutable f2))
  (or (eq? f2-immutable 'dont-care)
      (eq? f1-immutable f2-immutable)))

(define (vectorof->multi-vectorof ctc blame chap-not-imp?)
  (cond
    [(multi-vectorof? ctc) ; already space efficient
     ctc]
    [(and (base-vectorof? ctc) (contract-has-space-efficient-support? ctc))
     (define elem (base-vectorof-elem ctc))
     (define set-blame (blame-swap blame))
     ((if chap-not-imp? chaperone-multi-vectorof impersonator-multi-vectorof)
      (vectorof->multi-vectorof elem blame chap-not-imp?)
      (vectorof->multi-vectorof elem set-blame chap-not-imp?)
      (list (first-order-check (base-vectorof-immutable ctc) blame))
      blame
      ctc)]
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
     (define chap/imp/c
       (cond [(chaperone-multi-vectorof? new-multi)
              (unless (chaperone-multi-vectorof? old-multi)
                (error "internal error: joining chaperone and impersonator contracts"
                       new-multi old-multi))
              chaperone-multi-vectorof]
             [else
              impersonator-multi-vectorof]))
     (chap/imp/c
      (join-multi-vectorof (multi-vectorof-ref-ctc new-multi)
                           (multi-vectorof-ref-ctc old-multi))
      (join-multi-vectorof (multi-vectorof-set-ctc old-multi)
                           (multi-vectorof-set-ctc new-multi))
      (first-order-check-join (multi-vectorof-first-order old-multi)
                              (multi-vectorof-first-order new-multi))
      (multi-vectorof-latest-blame new-multi)
      (multi-vectorof-latest-ctc new-multi))]
    [(multi-vectorof? old-multi)
     (multi-leaf/c-join new-multi (multi->leaf old-multi))]
    [(multi-vectorof? new-multi)
     (multi-leaf/c-join (multi->leaf new-multi) old-multi)]
    [else
     (multi-leaf/c-join new-multi old-multi)]))

(define (vectorof-space-efficient-guard ctc val blame chap-not-imp?)
  (define (make-checking-wrapper unwrapped)
    (if chap-not-imp?
        (chaperone-vector* unwrapped chaperone-ref-wrapper chaperone-set-wrapper)
        (impersonate-vector* unwrapped impersonator-ref-wrapper impersonator-set-wrapper)))
  (define-values (merged-ctc checking-wrapper)
    (cond [(has-impersonator-prop:multi/c? val)
           (unless (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting a checking wrapper" val))
           (values (join-multi-vectorof (vectorof->multi-vectorof ctc blame chap-not-imp?)
                                        (get-impersonator-prop:multi/c val))
                   (get-impersonator-prop:checking-wrapper val))]
          [(has-contract? val)
           (when (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting no checking wrapper" val))
           (define orig-ctc (value-contract val))
           (define orig-blame (value-blame val))
           (define unwrapped ;; un-contracted (since it is wrapped in a chaperone)
             ((if chap-not-imp?
                  unsafe-chaperone-vector
                  unsafe-impersonate-vector)
              val
              (get-impersonator-prop:unwrapped val)))
           (values (join-multi-vectorof
                    (vectorof->multi-vectorof ctc blame chap-not-imp?)
                    (vectorof->multi-vectorof orig-ctc orig-blame chap-not-imp?))
                   (make-checking-wrapper unwrapped))]
          [else
           (unless (multi-vectorof? ctc)
             (error "internal error: expecting a space-efficient contract" ctc))
           (when (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting no checking wrapper" val))
           (values ctc (make-checking-wrapper val))]))
  (define chap/imp (if chap-not-imp? chaperone-vector impersonate-vector))
  (define b (box #f))
  (define res
    (chap/imp
     checking-wrapper
     #f
     #f
     impersonator-prop:checking-wrapper checking-wrapper
     impersonator-prop:outer-wrapper-box b
     impersonator-prop:multi/c merged-ctc
     impersonator-prop:contracted  (multi-vectorof-latest-ctc merged-ctc)
     impersonator-prop:blame (multi-vectorof-latest-blame merged-ctc)))
  (set-box! b res)
  res)

;; Apply a list of projections over a value
;; Note that for our purposes it is important to fold left otherwise blame
;; could be assigned in the wrong order
;; [a -> (Maybe a)] -> a -> (Maybe a)
(define (apply-proj-list proj-list val)
  (foldl (lambda (f v) (f v #f)) val proj-list)) ; #f neg-party (already in blame)

(define (guard-multi/c ctc val chap-not-imp?)
  (unless (multi/c? ctc)
    (error "internal error: not a space-efficient contract"))
  (cond
    [(multi-leaf/c? ctc)
     (apply-proj-list (multi-leaf/c-proj-list ctc) val)]
    [(value-has-vectorof-space-efficient-support? val chap-not-imp?)
     (do-first-order-checks ctc val)
     (vectorof-space-efficient-guard ctc val (multi-vectorof-latest-blame ctc) chap-not-imp?)]
    [else
     (bail-to-regular-wrapper ctc val chap-not-imp?)]))


(define (chaperone-ref-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define ref-ctc (multi-vectorof-ref-ctc ctc))
  (define blame (multi-vectorof-latest-blame ctc))
  (with-space-efficient-contract-continuation-mark
    (with-contract-continuation-mark
      blame
      (guard-multi/c ref-ctc elt #t))))

(define (chaperone-set-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define set-ctc (multi-vectorof-set-ctc ctc))
  (define blame (multi-vectorof-latest-blame ctc))
  (with-space-efficient-contract-continuation-mark
    (with-contract-continuation-mark
      blame
      (guard-multi/c set-ctc elt #t))))

(define (impersonator-ref-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define ref-ctc (multi-vectorof-ref-ctc ctc))
  (define blame (multi-vectorof-latest-blame ctc))
  (with-space-efficient-contract-continuation-mark
    (with-contract-continuation-mark
      blame
      (guard-multi/c ref-ctc elt #f))))

(define (impersonator-set-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define set-ctc (multi-vectorof-set-ctc ctc))
  (define blame (multi-vectorof-latest-blame ctc))
  (with-space-efficient-contract-continuation-mark
    (with-contract-continuation-mark
      blame
      (guard-multi/c set-ctc elt #f))))
  
(define (bail-to-regular-wrapper m/c val chap-not-imp?)
  (do-first-order-checks m/c val)
  (define blame (multi-vectorof-latest-blame m/c))
  (define ctc (multi-vectorof-latest-ctc m/c))
  (if chap-not-imp?
      (chaperone-vector*
       val
       chaperone-ref-wrapper
       chaperone-set-wrapper
       impersonator-prop:contracted ctc
       impersonator-prop:blame blame)
      (impersonate-vector*
       val
       impersonator-ref-wrapper
       impersonator-set-wrapper
       impersonator-prop:contracted ctc
       impersonator-prop:blame blame)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; vector/c
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(provide (struct-out base-vector/c)
         vector/c-space-efficient-guard
         value-has-vector/c-space-efficient-support?
         )

(module+ for-testing
  (provide multi-vector/c multi-vector/c-ref-ctcs multi-vector/c-set-ctcs
           value-has-vector/c-space-efficient-support?))


;; borrowed from vector.rkt as with vectorof
;; TODO: make vector-common.rkt to lift the needed common definitions
(define-struct base-vector/c (elems immutable))


;; TODO: make space-efficient-common.rkt for the multi/c struct and friends
(struct multi-vector/c multi/c (ref-ctcs set-ctcs first-order latest-blame latest-ctc))
(struct chaperone-multi-vector/c multi-vector/c ())
(struct impersonator-multi-vector/c  multi-vector/c ())


;; TODO: might need new first-order-check structure because with vector/c
;;       checking length is now a first order check as well.
;; TODO: figure out a nice way to merge this with the vectorof first-order structure
(struct vector/c-first-order (immutable length blame))

(define (vector/c-first-order-check-stronger? f1 f2)
  (define f1-immutable (vector/c-first-order-immutable f1))
  (define f1-length (vector/c-first-order-length f1))
  (define f2-immutable (vector/c-first-order-immutable f2))
  (define f2-length (vector/c-first-order-length f2))
  (and (= f1-length f2-length)
       (or (eq? f2-immutable 'dont-care)
           (eq? f1-immutable f2-immutable))))

;; TODO: factor out the first order checks from vector.rkt
(define (do-vector/c-first-order-checks m/c val)
  (define checks (multi-vector/c-first-order m/c))
  (for ([check (in-list checks)])
    (define immutable (vector/c-first-order-immutable check))
    (define blame (vector/c-first-order-blame check))
    (define length (vector/c-first-order-length check))
    (do-check-vector/c val blame immutable length)))


;; TODO: this is lifted and modified from vector.rkt, it would be better to abstract these
;; into a common function
(define (do-check-vector/c val blame immutable length)
  (unless (vector? val)
    (raise-blame-error blame #:missing-party #f val
                       '(expected: "a vector" given: "~e") val))
  (cond
    [(eq? immutable #t)
     (unless (immutable? val)
       (raise-blame-error blame #:missing-party #f val
                          '(expected: "an immutable vector" given: "~e")
                          val))]
    [(eq? immutable #f)
     (when (immutable? val)
       (raise-blame-error blame #:missing-party #f val
                          '(expected: "a mutable vector" given: "~e")
                          val))]
    [else (void)])
  (unless (= (vector-length val) length)
    (raise-blame-error blame #:missing-party #f val
                       '(expected: "a vector of ~a element~a" given: "~e")
                       length
                       (if (= length 1) "" "s")
                       val)))

;; TODO: refactor this with the vectorof version
(define (vector/c-first-order-check-join new-checks old-checks)
  (append new-checks
          (for/list ([old (in-list old-checks)]
                     #:when (not (implied-by-one?
                                  new-checks old
                                  #:implies vector/c-first-order-check-stronger?)))
            old)))

;; TODO: this is the same as the vectorof function, should these actually be the same???
;; if so, then just need one, else can abstract most of the common parts
(define (value-has-vector/c-space-efficient-support? val chap-not-imp?)
  (define (bail reason)
    (when debug-bailouts
      (printf "value bailing: ~a -- ~a\n" reason val))
    #f)
  (and (or (vector? val)
           ;; TODO: is this enough checking for vector/c support? what about length?
           (bail "not a vector"))
       (or (if (has-impersonator-prop:unwrapped? val)
               (not (impersonator? (get-impersonator-prop:unwrapped val)))
               #t)
           (bail "already chaperoned"))
       (or (if (has-impersonator-prop:outer-wrapper-box? val)
               (eq? val (unbox (get-impersonator-prop:outer-wrapper-box val)))
               #t)
           (bail "has been chaperoned since last contracted"))
       ;; disallow switching between chaperone and impersonator wrappers
       (or (cond [(has-impersonator-prop:checking-wrapper? val)
                  (define checking-wrapper
                    (get-impersonator-prop:checking-wrapper val))
                  (if (chaperone? checking-wrapper)
                      chap-not-imp?
                      (not chap-not-imp?))]
                 [else
                  (if chap-not-imp?
                      (chaperone-contract?    (value-contract val))
                      (impersonator-contract? (value-contract val)))])
           (bail "switching from imp to chap or vice versa"))))

(define (vector/c->multi-vector/c ctc blame chap-not-imp?)
  (cond
    [(multi-vector/c? ctc) ; already space efficient
     ctc]
    ;; TODO: I think we just support ALL vector contracts in space efficient mode
    ;;       so this check always returns #t ...
    [(and (base-vector/c? ctc) (contract-has-space-efficient-support? ctc))
     (define elems (base-vector/c-elems ctc))
     (define set-blame (blame-swap blame))
     ((if chap-not-imp? chaperone-multi-vector/c impersonator-multi-vector/c)
      (for/list ([elem-ctc (in-list elems)])
        (vector/c->multi-vector/c elem-ctc blame chap-not-imp?))
      (for/list ([elem-ctc (in-list elems)])
        (vector/c->multi-vector/c elem-ctc set-blame chap-not-imp?))
      (list (vector/c-first-order
             (base-vector/c-immutable ctc)
             (length elems)
             blame))
      blame
      ctc)]
    [else ; convert to a leaf
     (multi-leaf/c
      (list ((contract-late-neg-projection ctc) blame))
      (list ctc))]))

(define (join-multi-vector/c new-multi old-multi)
  ;; TODO: lift this out to a single top-level definition shared amongst
  ;; the space-efficient implementations.
  (define (multi->leaf c)
    (multi-leaf/c
     ;; create a regular projection from the multi wrapper
     (list (λ (val neg-party)
             (bail-to-regular-wrapper c val
                                      (or (chaperone-multi-vector/c? old-multi)
                                          (chaperone-multi-vector/c? new-multi)))))
     ;; incomparable value for `contract-stronger?`
     (list (gensym))))
  (cond
    [(and (multi-vector/c? old-multi) (multi-vector/c? new-multi))
     (define chap/imp/c
       (cond [(chaperone-multi-vector/c? new-multi)
              (unless (chaperone-multi-vector/c? old-multi)
                (error "internal error: joining chaperone and impersonator contracts"
                       new-multi old-multi))
              chaperone-multi-vector/c]
             [else
              impersonator-multi-vector/c]))
     (chap/imp/c
      (for/list ([new (multi-vector/c-ref-ctcs new-multi)]
                 [old (multi-vector/c-ref-ctcs old-multi)])
        (join-multi-vector/c new old))
      (for/list ([new (multi-vector/c-set-ctcs new-multi)]
                 [old (multi-vector/c-set-ctcs old-multi)])
        (join-multi-vector/c old new))
      ;; this can/should be generalized
      (vector/c-first-order-check-join (multi-vector/c-first-order old-multi)
                                       (multi-vector/c-first-order new-multi))
      (multi-vector/c-latest-blame new-multi)
      (multi-vector/c-latest-ctc new-multi))]
    [(multi-vector/c? old-multi)
     (multi-leaf/c-join new-multi (multi->leaf old-multi))]
    [(multi-vector/c? new-multi)
     (multi-leaf/c-join (multi->leaf new-multi) old-multi)]
    [else
     (multi-leaf/c-join new-multi old-multi)]))

(define (vector/c-space-efficient-guard ctc val blame chap-not-imp?)
  (define (make-checking-wrapper unwrapped)
    (if chap-not-imp?
        (chaperone-vector*
         unwrapped
         vector/c-chaperone-ref-wrapper
         vector/c-chaperone-set-wrapper)
        (impersonate-vector*
         unwrapped
         vector/c-impersonator-ref-wrapper
         vector/c-impersonator-set-wrapper)))
  (define-values (merged-ctc checking-wrapper)
    (cond [(has-impersonator-prop:multi/c? val)
           (unless (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting a checking wrapper" val))
           (values (join-multi-vector/c (vector/c->multi-vector/c ctc blame chap-not-imp?)
                                        (get-impersonator-prop:multi/c val))
                   (get-impersonator-prop:checking-wrapper val))]
          [(has-contract? val)
           (when (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting no checking wrapper" val))
           (define orig-ctc (value-contract val))
           (define orig-blame (value-blame val))
           (define unwrapped ;; un-contracted (since it is wrapped in a chaperone)
             ((if chap-not-imp?
                  unsafe-chaperone-vector
                  unsafe-impersonate-vector)
              val
              (get-impersonator-prop:unwrapped val)))
           (values (join-multi-vector/c
                    (vector/c->multi-vector/c ctc blame chap-not-imp?)
                    (vector/c->multi-vector/c orig-ctc orig-blame chap-not-imp?))
                   (make-checking-wrapper unwrapped))]
          [else
           (unless (multi-vector/c? ctc)
             (error "internal error: expecting a space-efficient contract" ctc))
           (when (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting no checking wrapper" val))
           (values ctc (make-checking-wrapper val))]))
  (define chap/imp (if chap-not-imp? chaperone-vector impersonate-vector))
  (define b (box #f))
  (define res
    (chap/imp
     checking-wrapper
     #f
     #f
     impersonator-prop:checking-wrapper checking-wrapper
     impersonator-prop:outer-wrapper-box b
     impersonator-prop:multi/c merged-ctc
     impersonator-prop:contracted (multi-vector/c-latest-ctc merged-ctc)
     impersonator-prop:blame (multi-vector/c-latest-blame merged-ctc)))
  (set-box! b res)
  res)

(define (guard-multi-vector/c ctc val chap-not-imp?)
  (unless (multi/c? ctc)
    (error "internal error: not a space-efficient contract"))
  (cond
    [(multi-leaf/c? ctc)
     (apply-proj-list (multi-leaf/c-proj-list ctc) val)]
    [(value-has-vector/c-space-efficient-support? val chap-not-imp?)
     (do-vector/c-first-order-checks ctc val)
     (vector/c-space-efficient-guard ctc val (multi-vector/c-latest-blame ctc) chap-not-imp?)]
    [else
     (bail-to-regular-vector/c-wrapper ctc val chap-not-imp?)]))

;; TODO: list-ref seems inefficient here, figure out
;; how to replace with vector-ref
(define (vector/c-chaperone-ref-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define ref-ctcs (multi-vector/c-ref-ctcs ctc))
  (define ref-ctc (list-ref ref-ctcs i))
  (define blame (multi-vector/c-latest-blame ctc))
  (with-space-efficient-contract-continuation-mark
    (with-contract-continuation-mark
      blame
      (guard-multi-vector/c ref-ctc elt #t))))

(define (vector/c-chaperone-set-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define set-ctcs (multi-vector/c-set-ctcs ctc))
  (define set-ctc (list-ref set-ctcs i))
  (define blame (multi-vector/c-latest-blame ctc))
  (with-space-efficient-contract-continuation-mark
    (with-contract-continuation-mark
      blame
      (guard-multi-vector/c set-ctc elt #t))))

(define (vector/c-impersonator-ref-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define ref-ctcs (multi-vector/c-ref-ctcs ctc))
  (define ref-ctc (list-ref ref-ctcs i))
  (define blame (multi-vector/c-latest-blame ctc))
  (with-space-efficient-contract-continuation-mark
    (with-contract-continuation-mark
      blame
      (guard-multi-vector/c ref-ctc elt #f))))

(define (vector/c-impersonator-set-wrapper outermost v i elt)
  (define ctc (get-impersonator-prop:multi/c outermost))
  (define set-ctcs (multi-vector/c-set-ctcs ctc))
  (define set-ctc (list-ref set-ctcs i))
  (define blame (multi-vector/c-latest-blame ctc))
  (with-space-efficient-contract-continuation-mark
    (with-contract-continuation-mark
      blame
      (guard-multi-vector/c set-ctc elt #f))))

(define (bail-to-regular-vector/c-wrapper m/c val chap-not-imp?)
  (do-vector/c-first-order-checks m/c val)
  (define blame (multi-vector/c-latest-blame m/c))
  (define ctc (multi-vector/c-latest-ctc m/c))
  (if chap-not-imp?
      (chaperone-vector*
       val
       vector/c-chaperone-ref-wrapper
       vector/c-chaperone-set-wrapper
       impersonator-prop:contracted ctc
       impersonator-prop:blame blame)
      (impersonate-vector*
       val
       vector/c-impersonator-ref-wrapper
       vector/c-impersonator-set-wrapper
       impersonator-prop:contracted ctc
       impersonator-prop:blame blame)))
