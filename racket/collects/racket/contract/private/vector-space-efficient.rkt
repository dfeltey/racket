#lang racket/base

(require "prop.rkt" "guts.rkt" "blame.rkt" "vector-common.rkt"
         "space-efficient-common.rkt"
         (submod "space-efficient-common.rkt" properties)
         (only-in racket/unsafe/ops unsafe-chaperone-vector unsafe-impersonate-vector)
         (for-syntax racket/base))

(provide build-s-e-vector
         vector-space-efficient-guard
         add-vector-space-efficient-wrapper)

(module+ for-testing
  (provide  multi-vector? multi-vector-ref-ctcs multi-vector-set-ctcs))

(struct vector-first-order-check (immutable length blame missing-party))
(struct multi-vector multi-ho/c (first-order ref-ctcs set-ctcs))

(define (do-vector-first-order-checks m/c val neg-party)
  (define checks (multi-vector-first-order m/c))
  (for ([c (in-list checks)])
    (define immutable (vector-first-order-check-immutable c))
    (define length (vector-first-order-check-length c))
    (define blame (vector-first-order-check-blame c))
    (define neg (or (vector-first-order-check-missing-party c) neg-party))
    (check-vector/c val blame immutable length neg)))

(define (vector-first-order-check-stronger? f1 f2)
  (define f1-immutable (vector-first-order-check-immutable f1))
  (define f1-length (vector-first-order-check-length f1))
  (define f2-immutable (vector-first-order-check-immutable f2))
  (define f2-length (vector-first-order-check-length f2))
  (and (or (eq? f2-immutable 'dont-care)
           (eq? f1-immutable f2-immutable))
       (or (not f2-length)
           (and f1-length (= f1-length f2-length)))))

(define (build-s-e-vector s-e-pos s-e-neg ctc blame chap?)
  (define focs (build-vector-first-order-checks ctc blame))
  (if chap?
      (chaperone-multi-vector blame #f ctc (list focs) s-e-pos s-e-neg)
      (impersonator-multi-vector blame #f ctc (list focs) s-e-pos s-e-neg)))

(define (build-vector-first-order-checks ctc blame)
  (cond
    [(base-vectorof? ctc)
     (vector-first-order-check
      (base-vectorof-immutable ctc)
      #f
      blame
      #f)]
    [(base-vector/c? ctc)
     (vector-first-order-check
      (base-vector/c-immutable ctc)
      (length (base-vector/c-elems ctc))
      blame
      #f)]))

(define (add-f-o-neg-party focs neg-party)
  (for/list ([foc (in-list focs)])
    (define missing-party (vector-first-order-check-missing-party foc))
    (struct-copy
     vector-first-order-check
     foc
     [missing-party (or missing-party neg-party)])))
   
(define (vector-try-merge new-multi new-neg old-multi old-neg)
  (define constructor (get-constructor new-multi old-multi))
  (define merged
    (and constructor
         (constructor
          (multi-ho/c-latest-blame new-multi)
          (or (multi-ho/c-missing-party new-multi) new-neg)
          (multi-ho/c-latest-ctc new-multi)
          (first-order-check-join (add-f-o-neg-party (multi-vector-first-order old-multi) old-neg)
                                  (add-f-o-neg-party (multi-vector-first-order new-multi) new-neg)
                                  vector-first-order-check-stronger?)
          (merge* (multi-vector-ref-ctcs new-multi)
                  new-neg
                  (multi-vector-ref-ctcs old-multi)
                  old-neg)
          (merge* (multi-vector-set-ctcs old-multi)
                  old-neg
                  (multi-vector-set-ctcs new-multi)
                  new-neg))))
  (values merged #f))

(define (merge* new new-neg old old-neg)
  (cond
    [(and (vector? new) (vector? old))
     (for/vector ([nc (in-vector new)]
                  [oc (in-vector old)])
       (define-values (merged _) (merge nc new-neg oc old-neg))
       merged)]
    [(vector? new)
     (for/vector ([nc (in-vector new)])
       (define-values (merged _) (merge nc new-neg old old-neg))
       merged)]
    [(vector? old)
     (for/vector ([oc (in-vector old)])
       (define-values (merged _) (merge new new-neg oc old-neg))
       merged)]
    [else
     (define-values (merged _) (merge new new-neg old old-neg))
     merged]))

(define (get-constructor new old)
  (or (and (chaperone-multi-vector? new)
           (chaperone-multi-vector? old)
           chaperone-multi-vector)
      (and (impersonator-multi-vector? new)
           (impersonator-multi-vector? old)
           impersonator-multi-vector)))

(define (vector-space-efficient-guard s-e val neg-party)
  (do-vector-first-order-checks s-e val neg-party)
  (define chap-not-imp? (chaperone-multi-vector? s-e))
  (cond
    [(value-safe-for-space-efficient-mode? val chap-not-imp?)
     (add-vector-space-efficient-wrapper s-e val neg-party chap-not-imp?)]
    [else (bail-to-regular-wrapper s-e val neg-party)]))

(define (add-vector-space-efficient-wrapper s-e val neg-party chap-not-imp?)
  (define-values (merged-s-e new-neg checking-wrapper)
    (cond
      [(has-impersonator-prop:checking-wrapper? val)
       (define s-e-prop (get-impersonator-prop:space-efficient val))
       (define-values (merged-s-e new-neg)
         (vector-try-merge s-e neg-party (car s-e-prop) (cdr s-e-prop)))
       (values merged-s-e
               new-neg
               (get-impersonator-prop:checking-wrapper val))]
      [else
       (values s-e neg-party (make-checking-wrapper val chap-not-imp?))]))
  (cond
    [merged-s-e
     (define chap/imp (if chap-not-imp? chaperone-vector impersonate-vector))
     (define b (box #f))
     (define res
       (chap/imp
        checking-wrapper
        #f
        #f
        impersonator-prop:checking-wrapper checking-wrapper
        impersonator-prop:outer-wrapper-box b
        impersonator-prop:space-efficient (cons merged-s-e new-neg)
        impersonator-prop:contracted (multi-ho/c-latest-ctc merged-s-e)
        impersonator-prop:blame (blame-add-missing-party (multi-ho/c-latest-blame merged-s-e) neg-party)))
     (set-box! b res)
     res]
    [else (bail-to-regular-wrapper s-e val neg-party)]))

(define (make-checking-wrapper unwrapped chap-not-imp?)
  (if chap-not-imp?
      (chaperone-vector* unwrapped ref-wrapper set-wrapper)
      (impersonate-vector* unwrapped ref-wrapper set-wrapper)))

(define-syntax (make-vectorof-checking-wrapper stx)
  (syntax-case stx ()
    [(_ set? maybe-closed-over-m/c)
     #`(λ (outermost v i elt)
         (define prop
           #,(if (syntax-e #'maybe-closed-over-m/c)
                 #'maybe-closed-over-m/c
                 #'(get-impersonator-prop:space-efficient outermost)))
         (define m/c (car prop))
         (define neg (or (multi-ho/c-missing-party m/c) (cdr prop)))
         (define field
           #,(if (syntax-e #'set?)
                 #'(multi-vector-set-ctcs m/c)
                 #'(multi-vector-ref-ctcs m/c)))
         (define s-e
           (if (vector? field) (vector-ref field i) field))
         (define blame (blame-add-missing-party (multi-ho/c-latest-blame m/c) neg))
         (with-space-efficient-contract-continuation-mark
           (with-contract-continuation-mark
             blame
             (space-efficient-guard s-e elt neg))))]))

(define ref-wrapper (make-vectorof-checking-wrapper #f #f))
(define set-wrapper (make-vectorof-checking-wrapper #t #f))

(define (bail-to-regular-wrapper m/c val neg-party)
  (define chap-not-imp? (chaperone-multi-vector? m/c))
  (define neg (or (multi-ho/c-missing-party m/c) neg-party))
  (define blame (blame-add-missing-party (multi-ho/c-latest-blame m/c) neg))
  (define ctc (multi-ho/c-latest-ctc m/c))
  ((if chap-not-imp? chaperone-vector* impersonate-vector*)
   val
   (make-vectorof-checking-wrapper #f (cons m/c neg-party))
   (make-vectorof-checking-wrapper #t (cons m/c neg-party))
   impersonator-prop:contracted ctc
   impersonator-prop:blame blame
   impersonator-prop:unwrapped val))

(define (get-projection ctc)
  (lambda (val neg)
    (do-vector-first-order-checks ctc val neg)
    (bail-to-regular-wrapper ctc val neg)))

(define (vector-space-efficient-contract-property chap-not-imp?)
  (build-space-efficient-contract-property
   #:try-merge vector-try-merge
   #:space-efficient-guard vector-space-efficient-guard
   #:get-projection get-projection))

(struct chaperone-multi-vector multi-vector ()
  #:property prop:space-efficient-contract (vector-space-efficient-contract-property #t))
(struct impersonator-multi-vector multi-vector ()
  #:property prop:space-efficient-contract (vector-space-efficient-contract-property #f))
