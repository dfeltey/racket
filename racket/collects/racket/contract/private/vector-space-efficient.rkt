#lang racket/base

(require "prop.rkt" "guts.rkt" "blame.rkt" "vector-common.rkt"
         "space-efficient-common.rkt"
         (submod "space-efficient-common.rkt" properties)
         (only-in racket/unsafe/ops unsafe-chaperone-vector unsafe-impersonate-vector)
         (for-syntax racket/base))

(provide vector-space-efficient-guard
         value-has-vector-space-efficient-support?
         contract-has-vector-space-efficient-support?)

(module+ for-testing
  (provide  multi-vector? multi-vector-ref-ctcs multi-vector-set-ctcs
            value-has-vector-space-efficient-support?))

(define debug-bailouts #f)

(struct first-order-check (immutable length blame))
(struct multi-vector multi-ho/c (first-order ref-ctcs set-ctcs))

(struct chaperone-multi-vector multi-vector ())
(struct impersonator-multi-vector multi-vector ())

(define (do-first-order-checks m/c val)
  (define checks (multi-vector-first-order m/c))
  (for ([c (in-list checks)])
    (define immutable (first-order-check-immutable c))
    (define length (first-order-check-length c))
    (define blame (first-order-check-blame c))
    (check-vector/c val blame immutable length)))

;; TODO: support and conversion can probably be unified into a single function
(define (contract-has-vector-space-efficient-support? ctc)
  (define (bail reason)
    (when debug-bailouts
      (printf "contract bailing: ~a -- ~a\n" reason ctc))
    #f)
  (or (multi-vector? ctc)
      ;; TODO: the problem is with turning higher order contracts into leaves
      ;; because that may drop negative position checks in the future leading to
      ;; incorrect blame
      (flat-contract? ctc)
      (and (base-vectorof? ctc)
           (contract-has-vector-space-efficient-support? (base-vectorof-elem ctc)))
      (and (base-vector/c? ctc)
           (for/and ([sub-ctc (in-list (base-vector/c-elems ctc))])
             (contract-has-vector-space-efficient-support? sub-ctc)))
      (bail "not a vector contract")))

(define (value-has-vector-space-efficient-support? val chap-not-imp?)
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
                  (or (not (value-contract val))
                      (if chap-not-imp?
                          (chaperone-contract?    (value-contract val))
                          (impersonator-contract? (value-contract val))))])
           (bail "switching from imp to chap or vice versa"))))

(define (first-order-check-stronger? f1 f2)
  (define f1-immutable (first-order-check-immutable f1))
  (define f1-length (first-order-check-length f1))
  (define f2-immutable (first-order-check-immutable f2))
  (define f2-length (first-order-check-length f2))
  (and (or (eq? f2-immutable 'dont-care)
           (eq? f1-immutable f2-immutable))
       (or (not f2-length)
           (and f1-length (= f1-length f2-length)))))

(define (vector-contract->multi-vector ctc blame chap-not-imp?)
  (define chap/imp
    (if chap-not-imp? chaperone-multi-vector impersonator-multi-vector))
  (cond
    [(multi-vector? ctc) ; already space efficient
     ctc]
    [(base-vectorof? ctc)
     (define elem (base-vectorof-elem ctc))
     (define set-blame (blame-swap blame))
     (chap/imp
      blame
      ctc
      (list (first-order-check (base-vectorof-immutable ctc) #f blame))
      (vector-contract->multi-vector elem blame chap-not-imp?)
      (vector-contract->multi-vector elem set-blame chap-not-imp?))]
    [(base-vector/c? ctc)
     (define elems (base-vector/c-elems ctc))
     (define set-blame (blame-swap blame))
     (chap/imp
      blame
      ctc
      (list (first-order-check
             (base-vector/c-immutable ctc)
             (length elems)
             blame))
      (for/vector ([elem-ctc (in-list elems)])
        (vector-contract->multi-vector elem-ctc blame chap-not-imp?))
      (for/vector ([elem-ctc (in-list elems)])
        (vector-contract->multi-vector elem-ctc set-blame chap-not-imp?)))]
    [else ; convert to a leaf
     (convert-to-multi-leaf/c ctc blame)]))

(define (first-order-check-join new-checks old-checks)
  (append new-checks
          (for/list ([old (in-list old-checks)]
                     #:when (not (implied-by-one?
                                  new-checks old
                                  #:implies first-order-check-stronger?)))
            old)))

(define (join-multi* new old)
  (cond
    [(and (multi/c? new) (multi/c? old)) (join-multi-vector new old)]
    [(and (vector? new) (vector? old))
     (for/vector ([nc (in-vector new)]
                  [oc (in-vector old)])
       (join-multi-vector nc oc))]
    [(vector? new)
     (for/vector ([nc (in-vector new)])
       (join-multi-vector nc old))]
    [(vector? old)
     (for/vector ([oc (in-vector old)])
       (join-multi-vector new oc))]
    [else
     (error "internal error: unexpected combination of space-efficient contracts" new old)]))

(define (join-multi-vector new-multi old-multi)
  (define (multi->leaf c)
    (multi-leaf/c
     ;; create a regular projection from the multi wrapper
     (list (λ (val neg-party)
             (bail-to-regular-wrapper c val
                                      (or (chaperone-multi-vector? old-multi)
                                          (chaperone-multi-vector? new-multi)))))
     ;; incomparable value for `contract-stronger?`
     (list (gensym))
     (list (multi-ho/c-latest-blame c))))
  (cond
    [(and (multi-vector? old-multi) (multi-vector? new-multi))
     (define chap/imp/c
       (cond [(chaperone-multi-vector? new-multi)
              (unless (chaperone-multi-vector? old-multi)
                (error "internal error: joining chaperone and impersonator contracts"
                       new-multi old-multi))
              chaperone-multi-vector]
             [else
              impersonator-multi-vector]))
     (chap/imp/c
      (multi-ho/c-latest-blame new-multi)
      (multi-ho/c-latest-ctc new-multi)
      (first-order-check-join (multi-vector-first-order old-multi)
                              (multi-vector-first-order new-multi))
      (join-multi* (multi-vector-ref-ctcs new-multi)
                   (multi-vector-ref-ctcs old-multi))
      (join-multi* (multi-vector-set-ctcs old-multi)
                   (multi-vector-set-ctcs new-multi)))]
    [(multi-vector? old-multi)
     (join-multi-leaf/c new-multi (multi->leaf old-multi))]
    [(multi-vector? new-multi)
     (join-multi-leaf/c (multi->leaf new-multi) old-multi)]
    [else
     (join-multi-leaf/c new-multi old-multi)]))

(define (vector-space-efficient-guard ctc val blame chap-not-imp?)
  (define (make-checking-wrapper unwrapped)
    (define chap/imp (if chap-not-imp? chaperone-vector* impersonate-vector*))
    (define ref-wrapper (if chap-not-imp? chaperone-ref-wrapper impersonator-ref-wrapper))
    (define set-wrapper (if chap-not-imp? chaperone-set-wrapper impersonator-set-wrapper))
    (chap/imp unwrapped ref-wrapper set-wrapper))
  (define-values (merged-ctc checking-wrapper)
    (cond [(has-impersonator-prop:multi/c? val)
           (unless (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting a checking wrapper" val))
           (values (join-multi-vector (vector-contract->multi-vector ctc blame chap-not-imp?)
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
           (values (join-multi-vector
                    (vector-contract->multi-vector ctc blame chap-not-imp?)
                    (vector-contract->multi-vector orig-ctc orig-blame chap-not-imp?))
                   (make-checking-wrapper unwrapped))]
          [else
           (unless (multi-vector? ctc)
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
     impersonator-prop:contracted  (multi-ho/c-latest-ctc merged-ctc)
     impersonator-prop:blame (multi-ho/c-latest-blame merged-ctc)))
  (set-box! b res)
  res)

(define (guard-multi/c ctc val chap-not-imp?)
  (unless (multi/c? ctc)
    (error "internal error: not a space-efficient contract"))
  (cond
    [(multi-leaf/c? ctc)
     (apply-proj-list (multi-leaf/c-proj-list ctc) val)]
    [(value-has-vector-space-efficient-support? val chap-not-imp?)
     (do-first-order-checks ctc val)
     (vector-space-efficient-guard ctc val (multi-ho/c-latest-blame ctc) chap-not-imp?)]
    [else
     (bail-to-regular-wrapper ctc val chap-not-imp?)]))

(define-syntax (make-vectorof-checking-wrapper stx)
  (syntax-case stx ()
    [(_ chap-not-imp? set? maybe-closed-over-m/c)
     #`(λ (outermost v i elt)
         (define m/c
           #,(if (syntax-e #'maybe-closed-over-m/c)
                 #'maybe-closed-over-m/c
                 #'(get-impersonator-prop:multi/c outermost)))
         (define field
           #,(if (syntax-e #'set?)
                 #'(multi-vector-set-ctcs m/c)
                 #'(multi-vector-ref-ctcs m/c)))
         (define ctc
           (if (vector? field) (vector-ref field i) field))
         (define blame (multi-ho/c-latest-blame m/c))
         (with-space-efficient-contract-continuation-mark
           (with-contract-continuation-mark
             blame
             (guard-multi/c ctc elt chap-not-imp?))))]))

(define chaperone-ref-wrapper (make-vectorof-checking-wrapper #t #f #f))
(define chaperone-set-wrapper (make-vectorof-checking-wrapper #t #t #f))
(define impersonator-ref-wrapper (make-vectorof-checking-wrapper #f #f #f))
(define impersonator-set-wrapper (make-vectorof-checking-wrapper #f #t #f))

(define (bail-to-regular-wrapper m/c val chap-not-imp?)
  (do-first-order-checks m/c val)
  (define blame (multi-ho/c-latest-blame m/c))
  (define ctc (multi-ho/c-latest-ctc m/c))
  ((if chap-not-imp? chaperone-vector* impersonate-vector*)
   val
   (make-vectorof-checking-wrapper chap-not-imp? #f m/c)
   (make-vectorof-checking-wrapper chap-not-imp? #t m/c)
   impersonator-prop:contracted ctc
   impersonator-prop:blame blame))
