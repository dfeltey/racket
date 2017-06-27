#lang racket/base

;; Space-efficient arrow contracts
;; supports a subset of full arrow contracts
;; based on a prototype by Christophe Scholliers

(require racket/unsafe/ops
         "space-efficient-common.rkt"
         (submod "space-efficient-common.rkt" properties)
         "prop.rkt" "guts.rkt" "misc.rkt" "blame.rkt" "arrow-common.rkt"
         "arity-checking.rkt"
         (for-syntax racket/base))

(provide space-efficient-guard
         contract-has-space-efficient-support?
         value-has-space-efficient-support?)
(module+ for-testing
  (provide multi->? multi->-doms multi->-rng
           value-has-space-efficient-support?))

;; General Strategy

;; Each function contracted with a space-efficient contract has two or three
;; chaperone wrappers.
;; - Functions that are wrapped in a "top-level" arrow contract (i.e., not a
;;   subcontract of an arrow contract) are first contracted using a regular
;;   function contract wrapper (before reaching this code). Upon being
;;   contracted a second time, they reach this code, and get three chaperone
;;   wrappers:
;;   - first, an unsafe-chaperone wrapper, which chaperones the current
;;     contracted value (to pretend it's it), but actually just calls the
;;     original, uncontracted function (i.e. skips the original contract)
;;   - second, a chaperone* wrapper, which gets passed the outermost wrapper,
;;     and looks at a property on it to figure out what to check, then does
;;     the actual contract checking
;;   - third, a property-only chaperone wrapper, which has a multi contract
;;     on a property, to keep track of which contracts to check.
;;   When additional contracts are applied, this third chaperone is swapped out
;;   for a new one, which keeps track of the new, merged contract to check.
;;   Because it's a property-only chaperone, replacing it with a new one doesn't
;;   affect chaperone-of-ness.
;; - Functions that are wrapped in an "internal node" arrow contract (i.e.,
;;   their arrow contract is a subcontract of another arrow contract) may be
;;   wrapped with space-efficient wrappers from the start (i.e., before getting
;;   any other contract).
;;   Note: This could be changed. Just avoid recursively converting contracts in
;;     `ho/c->multi->`, and instead have doms and rngs be `ho-leaf/c` always.
;;   Because of this, they don't need the first, unsafe chaperone wrapper above.
;;   They only have the last two wrappers, otherwise the above strategy applies.

;; Alternatively, we may try to attach an (internal node) space-efficient
;; contract to a value that doesn't support space-efficient contracts (e.g.,
;; a function that takes keyword arguments). In this case, we must fall back to
;; regular contract wrapping, and convert the space-efficient contract to a
;; regular checking wrapper, as used elsewhere in the contract system (c.f.
;; `bail-to-regular-wrapper`).


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Data structures

;; we store the most recent blame only. when contracts fail, they assign
;; blame based on closed-over blame info, so `latest-blame` is only used
;; for things like prop:blame, contract profiling, and tail marks, in which
;; case we lose information, but it's ok to be conservative in these places
;; (and this behavior is consistent with what would happen in the absence
;; of space-efficient contracts anyway)
;; ditto for `latest-ctc` and prop:contracted
(struct multi-> multi-ho/c (doms rng first-order-checks))
(struct chaperone-multi-> multi-> ())
(struct impersonator-multi-> multi-> ())

;; contains all the information necessary to both (1) perform first order checks
;; for an arrow contract, and (2) determine which such checks are redundant and
;; can be eliminated
(struct first-order-check (n-doms blame method?))
;; stronger really means "the same" here
(define (first-order-check-stronger? x y)
  (= (first-order-check-n-doms x) (first-order-check-n-doms y)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Applicability checks

(define debug-bailouts #f)

(define (contract-has-space-efficient-support? ctc)
  (define (bail reason)
    (when debug-bailouts
      (printf "contract bailing: ~a -- ~a\n" reason ctc))
    #f)
  (cond [(multi->? ctc) ; already one
         #t]
        [(base->? ctc) ; only applies to regular arrow contracts (for now)
         (define doms (base->-doms ctc))
         (define rngs (base->-rngs ctc))
         (and (or doms
                  (bail "no doms"))
              (or (= (length doms) (base->-min-arity ctc)) ; no optional args
                  (bail "has optional args"))
              (or (null? (base->-kwd-infos ctc)) ; no keyword args
                  (bail "has keyword args"))
              (or (not (base->-rest ctc)) ; no rest arg
                  (bail "has rest arg"))
              (or (not (base->-pre? ctc)) ; no pre-condition
                  (bail "has pre-condition"))
              (or (not (base->-post? ctc)) ; no post-condition
                  (bail "has post-condition"))
              (or rngs
                  (bail "no rngs"))
              (or (= (length rngs) 1)
                  (bail "multiple return values"))
              ;; subcontracts also have to support space-efficient mode
              (for/and ([d (in-list doms)])
                (if (base->? d)
                    (contract-has-space-efficient-support? d)
                    (or (flat-contract? d)
                        (bail "subcontract does not have space-efficient support"))))
              (if (base->? (car rngs))
                  (contract-has-space-efficient-support? (car rngs))
                  (or (flat-contract? (car rngs))
                      (bail "subcontract does not have space-efficient support"))))]
        [else
         (bail "not base arrow")
         #f]))

(define (value-has-space-efficient-support? val chap-not-imp?)
  (define (bail reason)
    (when debug-bailouts
      (printf "value bailing: ~a -- ~a\n" reason val))
    #f)
  (and (or (procedure? val)
           (bail "not a procedure"))
       ;; the interposition wrapper has to support a superset of the arity
       ;; of the function it's wrapping, and ours can't support optional
       ;; args, keywords, etc. so just bail out in these cases
       (or (integer? (procedure-arity val)) ; no optional arguments
           (bail "has optional args"))
       (or (let-values ([(man opt) (procedure-keywords val)]) ; no keyword arguments
             (and (null? man) (null? opt)))
           (bail "has keyword args"))
       (or (equal? (procedure-result-arity val) 1)
           (bail "can't prove single-return-value"))
       ;; unsafe-chaperone-procedure does not respect the chaperone-procedure*
       ;; protocol, so it's not safe to use it on something that's already
       ;; chaperoned with it (before it was contracted)
       (or (if (has-impersonator-prop:unwrapped? val)
               (not (procedure-impersonator*? (get-impersonator-prop:unwrapped val)))
               #t)
           (bail "already chaperoned"))
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Wrapper management and contract checking

;; (or/c contract? multi/c?) × α × blame? × boolean? → α
(define (space-efficient-guard ctc val blame chap-not-imp?)
  (define (make-checking-wrapper unwrapped) ; add 2nd chaperone, see above
    (if chap-not-imp?
        (chaperone-procedure*   unwrapped chaperone-wrapper)
        (impersonate-procedure* unwrapped impersonator-wrapper)))
  (define-values (merged-m/c checking-wrapper)
    (cond [(has-impersonator-prop:multi/c? val)
           ;; value is already in space-efficient mode; merge new contract in
           (unless (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting a checking wrapper" val))
           (values (join-multi-> (ho/c->multi-> ctc blame chap-not-imp?)
                                    (get-impersonator-prop:multi/c val))
                   (get-impersonator-prop:checking-wrapper val))]
          [(has-contract? val)
           ;; value is already contracted; switch to space-efficient mode
           (when (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting no checking wrapper" val))
           (define orig-ctc   (value-contract val))
           (define orig-blame (value-blame    val))
           ;; pretend we're the (once) contracted value, but bypass its checking
           ;; (1st chaperone, see above)
           (define unwrapped
             ((if chap-not-imp?
                  unsafe-chaperone-procedure
                  unsafe-impersonate-procedure)
              val
              (get-impersonator-prop:unwrapped val)))
           (values (join-multi->
                    (ho/c->multi-> ctc      blame chap-not-imp?)
                    (ho/c->multi-> orig-ctc orig-blame chap-not-imp?))
                   (make-checking-wrapper unwrapped))]
          [else
           ;; value is not contracted; applying a s-e subcontract directly
           (unless (multi/c? ctc)
             (error "internal error: expecting a space-efficient contract" ctc))
           (when (has-impersonator-prop:checking-wrapper? val)
             (error "internal error: expecting no checking wrapper" val))
           (values ctc (make-checking-wrapper val))])) ; already "unwrapped"
  ;; do the actual checking and wrap with the 3rd chaperone (see above)
  (define chap/imp (if chap-not-imp? chaperone-procedure impersonate-procedure))
  (define b (box #f)) ; to record the outermost (property-only) chaperone
  (define res
    (chap/imp
     checking-wrapper
     #f ; property-only, so we can swap it in and out
     impersonator-prop:checking-wrapper  checking-wrapper
     impersonator-prop:outer-wrapper-box b
     impersonator-prop:multi/c           merged-m/c
     ;; for these, latest is fine (and the behavior in the absence of s-e)
     impersonator-prop:contracted        (multi-ho/c-latest-ctc   merged-m/c)
     impersonator-prop:blame             (multi-ho/c-latest-blame merged-m/c)))
  (set-box! b res)
  res)

;; If requested, we can log the arities of the contracts that end up being
;; space-efficient. That can inform whether we should have arity-specific
;; wrappers, and if so, for which arities.
(define-logger space-efficient-contract-arrow-wrapper-arity)

;; Create the 2nd chaperone wrapper procedure (see comment at the top),
;; as well as "deoptimization" wrappers (see below).
;; Checking wrappers come in different varieties, along two axes:
;; - chaperone vs impersonator (to know how to wrap for subcontracts)
;; - where to find the checks (on an impersonator property, for actual
;;   space-efficient contracts, vs closed over, for cases where we need
;;   a regular contract wrapper (i.e., a subcontract has to "bail out,
;;   and can't use the space-efficient machinery (but since subcontracts
;;   always start-out as space-efficient, they can't bail out via the
;;   checks in arrow-higher-order, so we need to handle them here)))
(define-syntax (make-checking-wrapper stx)
  (syntax-case stx ()
    [(_ chap-not-imp? maybe-closed-over-m/c)
     ;; Note: it would be more efficient to have arity-specific wrappers here,
     ;;   as opposed to using a rest arg.
     #`(λ (outermost-chaperone . args)
         (define m/c
           #,(if (syntax-e #'maybe-closed-over-m/c)
                 #'maybe-closed-over-m/c ; we did close over the contract
                 ;; otherwise, get it from the impersonator property
                 #'(get-impersonator-prop:multi/c outermost-chaperone)))
         (define doms   (multi->-doms         m/c))
         (define rng    (multi->-rng          m/c))
         (define blame  (multi-ho/c-latest-blame m/c)) ; latest is ok here
         (define n-args (length args))
         (define n-doms (vector-length doms))
         (log-space-efficient-contract-arrow-wrapper-arity-info
          (number->string n-doms))
         (unless (= n-args n-doms)
           (raise-wrong-number-of-args-error blame outermost-chaperone
                                             n-args n-doms n-doms #f))
         ;; Note: to support (i.e., not bail on) functions that can't be proven
         ;;   to return a single value, have a `case-lambda` wrapper here. (With
         ;;   the possibility of using return-arity-specific wrappers if return
         ;;   arity happens to be known.)
         ;; Note: should add tail-marks-match support here.
         (define rng-checker
           (lambda (result)
             (with-space-efficient-contract-continuation-mark
               (with-contract-continuation-mark
                 blame
                 (guard-multi/c rng result chap-not-imp?)))))
         (apply values
                rng-checker
                (for/list ([dom (in-vector doms)]
                           [arg (in-list args)])
                  (with-space-efficient-contract-continuation-mark
                    (with-contract-continuation-mark
                      blame
                      (guard-multi/c dom arg chap-not-imp?))))))]))
(define chaperone-wrapper    (make-checking-wrapper #t #f))
(define impersonator-wrapper (make-checking-wrapper #f #f))

;; Apply a multi contract to a value
;; This is never called at the top level of the contract (only for subcontracts)
(define (guard-multi/c m/c val chap-not-imp?)
  (unless (multi/c? m/c)
    (error "internal error: not a space-efficient contract"))
  (cond [(multi-leaf/c? m/c)
         (apply-proj-list (multi-leaf/c-proj-list m/c) val)]
        ;; multi-> cases
        [(value-has-space-efficient-support? val chap-not-imp?)
         (do-first-order-checks m/c val)
         (space-efficient-guard
          m/c val (multi-ho/c-latest-blame m/c) chap-not-imp?)]
        [else
         ;; not safe to use space-efficient wrapping
         (bail-to-regular-wrapper m/c val chap-not-imp?)]))

;; create a regular checking wrapper from a space-efficient wrapper for a value
;; that can't use space-efficient wrapping
(define (bail-to-regular-wrapper m/c val chap-not-imp?)
  (do-first-order-checks m/c val)
  ((if chap-not-imp? chaperone-procedure* impersonate-procedure*)
   val
   (make-checking-wrapper chap-not-imp? m/c)
   impersonator-prop:contracted (multi-ho/c-latest-ctc   m/c)
   impersonator-prop:blame      (multi-ho/c-latest-blame m/c)))

(define (do-first-order-checks m/c val)
  (define checks (multi->-first-order-checks m/c))
  (for ([c (in-list checks)])
    (define n-doms (first-order-check-n-doms c))
    (cond [(do-arity-checking
            (first-order-check-blame c)
            val
            (for/list ([i (in-range n-doms)]) #f) ; has to have the right length
            #f ; no rest arg
            n-doms ; min-arity = max-arity
            '() ; no keywords
            (first-order-check-method? c))
           => (lambda (fail) (fail #f))])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Space-efficient contract data structure management

;; Convert a higher-order contract to a multi-higher-order contract
;; Conversion consists of simultaneously copying the structure of the
;; higher-order contract and propagating the blame to the leaves.
;; At the leaves we convert contracts to multi-leaf/c
(define (ho/c->multi-> ctc blame chap-not-imp?)
  (cond
   [(multi->? ctc) ; already in multi mode
    ctc]
   ;; copy structure and propagate blame
   [(and (base->? ctc) (contract-has-space-efficient-support? ctc))
    (define doms (base->-doms ctc))
    (define rng  (car (base->-rngs ctc))) ; assumes single range
    (define dom-blame (blame-swap blame))
    ((if chap-not-imp? chaperone-multi-> impersonator-multi->)
     blame
     ctc
     (for/vector ([dom (in-list doms)])
       (ho/c->multi-> dom dom-blame chap-not-imp?))
     (ho/c->multi-> rng blame chap-not-imp?)
     (list (first-order-check (length doms) blame (base->-method? ctc))))]
   [else ; anything else is wrapped in a multi-leaf wrapper
    (convert-to-multi-leaf/c ctc blame)]))

(define (join-first-order-check new-checks old-checks)
  (append new-checks
          (for/list ([old (in-list old-checks)]
                     #:when (or (not (implied-by-one?
                                      new-checks old
                                      #:implies first-order-check-stronger?))))
            old)))

;; join two multi->
(define (join-multi-> new-multi old-multi)
  (define (multi->leaf c)
    (multi-leaf/c
     ;; create a regular projection from the multi wrapper
     (list (lambda (val neg-party)
             (bail-to-regular-wrapper c val
                                      (or (chaperone-multi->? old-multi)
                                          (chaperone-multi->? new-multi)))))
     ;; nothing meaningful here. just want to be incomparable by
     ;; `contract-stronger?`
     (list (gensym))))
  (cond
   [(and (multi->? old-multi) (multi->? new-multi))
    (define chap/imp/c
      (cond [(chaperone-multi->? new-multi)
             (unless (chaperone-multi->? old-multi) ; shouldn't happen
               (error "internal error: joining chaperone and impersonator contracts"
                      new-multi old-multi))
             chaperone-multi->]
            [else
             impersonator-multi->]))
    (chap/imp/c
     (multi-ho/c-latest-blame new-multi)
     (multi-ho/c-latest-ctc   new-multi)
     ;; if old and new don't have the same arity, then one of them will *have*
     ;; to fail its first order checks, so we're fine.
     ;; (we don't support optional arguments)
     (for/vector ([new (in-vector (multi->-doms new-multi))]
                  [old (in-vector (multi->-doms old-multi))])
       (join-multi-> old new))
     (join-multi-> (multi->-rng new-multi)
                   (multi->-rng old-multi))
     (join-first-order-check (multi->-first-order-checks old-multi)
                             (multi->-first-order-checks new-multi)))]
   [(multi->? old-multi) ; convert old to a multi-leaf/c
    (join-multi-leaf/c new-multi (multi->leaf old-multi))]
   [(multi->? new-multi) ; convert new to a multi-leaf/c
    (join-multi-leaf/c (multi->leaf new-multi) old-multi)]
   [else
    (join-multi-leaf/c new-multi old-multi)]))
