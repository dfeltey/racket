#lang racket/base

(require "prop.rkt" "guts.rkt" "blame.rkt" "vector-common.rkt"
         "space-efficient-common.rkt"
         (submod "space-efficient-common.rkt" properties)
         (only-in racket/unsafe/ops unsafe-chaperone-vector unsafe-impersonate-vector)
         (for-syntax racket/base))

(provide build-s-e-vector)

(module+ for-testing
  (provide  multi-vector? multi-vector-ref-ctcs multi-vector-set-ctcs
            value-has-vector-space-efficient-support?))

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

(define (contract-has-vector-space-efficient-support? ctc)
  (or (multi-vector? ctc)
      (base-vectorof? ctc)
      (base-vector/c? ctc)
      (begin
        (log-space-efficient-contract-bailout-info "vector: not a vector contract")
        #f)))

(define ((val-has-vec-s-e-support? chap-not-imp?) val)
  (define-syntax-rule (bail reason)
    (begin
      (log-space-efficient-value-bailout-info (format "vector: ~a" reason))
      #f))
  (and (or (vector? val)
           (bail "not a vector"))
       #;(or (if (has-impersonator-prop:unwrapped? val)
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
                  ;; avoid calling value-contract here
                  (or (not (value-contract val))
                      (if chap-not-imp?
                          (chaperone-contract?    (value-contract val))
                          (impersonator-contract? (value-contract val))))])
           (bail "switching from imp to chap or vice versa"))))

(define (value-has-vector-space-efficient-support? val chap-not-imp?)
  ((val-has-vec-s-e-support? chap-not-imp?) val))

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
  ;; TODO: sometimes the first-order check are redundant ...
  (do-vector-first-order-checks s-e val neg-party)
  (define chap-not-imp? (chaperone-multi-vector? s-e))
  (cond
    ;; don't check this twice
    [((val-has-vec-s-e-support? chap-not-imp?) val)
     ;; no bound occurences
     (define blame (multi-ho/c-latest-blame s-e))
     (define (make-checking-wrapper unwrapped)
       (define chap/imp (if chap-not-imp? chaperone-vector* impersonate-vector*))
       (chap/imp unwrapped ref-wrapper set-wrapper))
     (define-values (merged-ctc new-neg checking-wrapper)
       (cond [(has-impersonator-prop:multi/c? val)
              ;; TODO: maybe unify multi/c and space-efficient props
              (unless (has-impersonator-prop:checking-wrapper? val)
                ;; FIXME: call to error
                (error "internal error: expecting a checking wrapper" val))
              (define prop (get-impersonator-prop:multi/c val))
              ;; try to make decisions once
              (define-values (merged neg)
                (try-merge s-e neg-party (car prop) (cdr prop)))
              (values merged
                      neg
                      (get-impersonator-prop:checking-wrapper val))]
             #;[(and (has-contract? val) (has-impersonator-prop:unwrapped? val))
              (when (has-impersonator-prop:checking-wrapper? val)
                (error "internal error: expecting no checking wrapper" val))
              ;; no left-left
              (define unwrapped ;; un-contracted (since it is wrapped in a chaperone)
                ((if chap-not-imp?
                     unsafe-chaperone-vector
                     unsafe-impersonate-vector)
                 val
                 (get-impersonator-prop:unwrapped val)))
              (define checking-wrapper (make-checking-wrapper unwrapped))
              (cond
                [(has-impersonator-prop:space-efficient? val)
                 ;; rearrange this, if we know it doesn't have the prop:s-e
                 ;; maybe this goes away if we don't need to mask the property
                 (define prop
                   (or (get-impersonator-prop:space-efficient val) (cons #f #f)))
                 (define-values (merged neg)
                   (try-merge s-e neg-party (car prop) (cdr prop)))
                 (values merged neg checking-wrapper)]
                [else ;; no space-efficient prop to merge with so bail
                 (values #f neg-party checking-wrapper)])]
             [else
              (when (has-impersonator-prop:checking-wrapper? val)
                (error "internal error: expecting no checking wrapper" val))
              (values s-e neg-party (make-checking-wrapper val))]))
     (cond
       [merged-ctc
        (define chap/imp (if chap-not-imp? chaperone-vector impersonate-vector))
        (define b (box #f))
        (define res
          (chap/imp
           checking-wrapper
           #f
           #f
           impersonator-prop:checking-wrapper checking-wrapper
           impersonator-prop:outer-wrapper-box b
           impersonator-prop:multi/c (cons merged-ctc new-neg)
           impersonator-prop:space-efficient (cons merged-ctc new-neg)
           impersonator-prop:contracted  (multi-ho/c-latest-ctc merged-ctc)
           impersonator-prop:blame (blame-add-missing-party
                                    (multi-ho/c-latest-blame merged-ctc)
                                    neg-party)))
        (set-box! b res)
        res]
       [else (bail-to-regular-wrapper s-e val neg-party)])]
    [else (bail-to-regular-wrapper s-e val neg-party)]))

(define-syntax (make-vectorof-checking-wrapper stx)
  (syntax-case stx ()
    [(_ set? maybe-closed-over-m/c)
     #`(λ (outermost v i elt)
         (define prop
           #,(if (syntax-e #'maybe-closed-over-m/c)
                 #'maybe-closed-over-m/c
                 #'(get-impersonator-prop:multi/c outermost)))
         (define m/c (car prop))
         (define neg (or (multi-ho/c-missing-party m/c) (cdr prop)))
         (define field
           #,(if (syntax-e #'set?)
                 #'(multi-vector-set-ctcs m/c)
                 #'(multi-vector-ref-ctcs m/c)))
         (define ctc
           (if (vector? field) (vector-ref field i) field))
         (define blame (blame-add-missing-party (multi-ho/c-latest-blame m/c) neg))
         (with-space-efficient-contract-continuation-mark
           (with-contract-continuation-mark
             blame
             (guard-multi/c ctc elt neg))))]))

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
   impersonator-prop:space-efficient #f
   impersonator-prop:unwrapped val))

(define (get-projection ctc)
  (lambda (val neg)
    (do-vector-first-order-checks ctc val neg)
    (bail-to-regular-wrapper ctc val neg)))

(define (vector-space-efficient-contract-property chap-not-imp?)
  (build-space-efficient-contract-property
   #:try-merge vector-try-merge
   #:value-has-space-efficient-support? (val-has-vec-s-e-support? chap-not-imp?)
   #:space-efficient-guard vector-space-efficient-guard
   #:get-projection get-projection))

(struct chaperone-multi-vector multi-vector ()
  #:property prop:space-efficient-contract (vector-space-efficient-contract-property #t))
(struct impersonator-multi-vector multi-vector ()
  #:property prop:space-efficient-contract (vector-space-efficient-contract-property #f))
