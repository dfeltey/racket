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

(provide arrow-space-efficient-guard
         ->-contract-has-space-efficient-support?
         value-has-space-efficient-support?
         ->-space-effificent-support-property)
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

(define ->-space-effificent-support-property
  (build-space-efficient-support-property
   #:has-space-efficient-support?
   (lambda (ctc) (->-contract-has-space-efficient-support? ctc))
   #:convert (lambda (ctc blame)
               (ho/c->multi-> ctc blame))))

(define ->-space-efficient-contract-property
  (build-space-efficient-contract-property
   #:try-merge (lambda (new old) (try-merge new old))
   #:space-efficient-guard (lambda (ctc val)
                             (arrow-space-efficient-guard ctc val))
   #:get-projection (lambda (ctc) (get-projection ctc))))

;; we store the most recent blame only. when contracts fail, they assign
;; blame based on closed-over blame info, so `latest-blame` is only used
;; for things like prop:blame, contract profiling, and tail marks, in which
;; case we lose information, but it's ok to be conservative in these places
;; (and this behavior is consistent with what would happen in the absence
;; of space-efficient contracts anyway)
;; ditto for `latest-ctc` and prop:contracted
(struct multi-> multi-ho/c (doms rng first-order-checks)
  #:property prop:space-efficient-support ->-space-effificent-support-property
  #:property prop:space-efficient-contract ->-space-efficient-contract-property)
(struct chaperone-multi-> multi-> ())
(struct impersonator-multi-> multi-> ())

;; contains all the information necessary to both (1) perform first order checks
;; for an arrow contract, and (2) determine which such checks are redundant and
;; can be eliminated
(struct arrow-first-order-check first-order-check (n-doms blame method?))
;; stronger really means "the same" here
(define (arrow-first-order-check-stronger? x y)
  (= (arrow-first-order-check-n-doms x) (arrow-first-order-check-n-doms y)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Applicability checks

(define debug-bailouts #f)

(define (->-contract-has-space-efficient-support? ctc)
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
                  (bail "multiple return values")))]
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

;; (or/c contract? multi/c?) × α × boolean? → α
(define (arrow-space-efficient-guard ctc val)
  (do-arrow-first-order-checks ctc val)
  (define chap-not-imp? (chaperone-multi->? ctc))
  (cond
    [(value-has-space-efficient-support? val chap-not-imp?)
     (define blame (multi-ho/c-latest-blame ctc))
     (define (make-checking-wrapper unwrapped) ; add 2nd chaperone, see above
       (if chap-not-imp?
           (chaperone-procedure*   unwrapped arrow-wrapper)
           (impersonate-procedure* unwrapped arrow-wrapper)))
     (define-values (merged-m/c checking-wrapper)
       (cond [(has-impersonator-prop:multi/c? val)
              ;; value is already in space-efficient mode; merge new contract in
              (unless (has-impersonator-prop:checking-wrapper? val)
                (error "internal error: expecting a checking wrapper" val))
              (values (merge
                       ctc
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
              (values (merge
                       ctc
                       (contract->space-efficient-contract orig-ctc orig-blame))
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
     res]
    [else (bail-to-regular-wrapper ctc val)]))

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
    [(_ maybe-closed-over-m/c)
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
                 (guard-multi/c rng result)))))
         (apply values
                rng-checker
                (for/list ([dom (in-vector doms)]
                           [arg (in-list args)])
                  (with-space-efficient-contract-continuation-mark
                    (with-contract-continuation-mark
                      blame
                      (guard-multi/c dom arg))))))]))

(define arrow-wrapper (make-checking-wrapper #f))

;; create a regular checking wrapper from a space-efficient wrapper for a value
;; that can't use space-efficient wrapping
(define (bail-to-regular-wrapper m/c val)
  (define chap-not-imp? (chaperone-multi->? m/c))
  ((if chap-not-imp? chaperone-procedure* impersonate-procedure*)
   val
   (make-checking-wrapper m/c)
   impersonator-prop:contracted (multi-ho/c-latest-ctc   m/c)
   impersonator-prop:blame      (multi-ho/c-latest-blame m/c)))

(define (do-arrow-first-order-checks m/c val)
  (define checks (multi->-first-order-checks m/c))
  (for ([c (in-list checks)])
    (define n-doms (arrow-first-order-check-n-doms c))
    (cond [(do-arity-checking
            (arrow-first-order-check-blame c)
            val
            (for/list ([i (in-range n-doms)]) #f) ; has to have the right length
            #f ; no rest arg
            n-doms ; min-arity = max-arity
            '() ; no keywords
            (arrow-first-order-check-method? c))
           => (lambda (fail) (fail #f))])))

(define (get-projection ctc)
  (lambda (val neg-party)
    (do-arrow-first-order-checks ctc val)
    (bail-to-regular-wrapper ctc val)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Space-efficient contract data structure management

;; Convert a higher-order contract to a multi-higher-order contract
;; Conversion consists of simultaneously copying the structure of the
;; higher-order contract and propagating the blame to the leaves.
;; At the leaves we convert contracts to multi-leaf/c
(define (ho/c->multi-> ctc blame)
  (define chap-not-imp? (chaperone-contract? ctc))
  (cond
   [(multi->? ctc) ; already in multi mode
    ctc]
   ;; copy structure and propagate blame
   [(and (base->? ctc) (->-contract-has-space-efficient-support? ctc))
    (define doms (base->-doms ctc))
    (define rng  (car (base->-rngs ctc))) ; assumes single range
    (define dom-blame (blame-swap blame))
    ((if chap-not-imp? chaperone-multi-> impersonator-multi->)
     blame
     ctc
     (for/vector ([dom (in-list doms)])
       (contract->space-efficient-contract dom dom-blame))
     (contract->space-efficient-contract rng blame)
     (list (arrow-first-order-check (length doms) blame (base->-method? ctc))))]
   [else ; anything else is wrapped in a multi-leaf wrapper
    (convert-to-multi-leaf/c ctc blame)]))

;; merge two multi->
(define (try-merge new-multi old-multi)
  (define constructor (get-constructor new-multi old-multi))
  (and constructor
       (constructor
        (multi-ho/c-latest-blame new-multi)
        (multi-ho/c-latest-ctc   new-multi)
        ;; if old and new don't have the same arity, then one of them will *have*
        ;; to fail its first order checks, so we're fine.
        ;; (we don't support optional arguments)
        (for/vector ([new (in-vector (multi->-doms new-multi))]
                     [old (in-vector (multi->-doms old-multi))])
          (merge old new))
        (merge (multi->-rng new-multi) (multi->-rng old-multi))
        (first-order-check-join (multi->-first-order-checks old-multi)
                                (multi->-first-order-checks new-multi)
                                arrow-first-order-check-stronger?))))

(define (get-constructor new old)
  (or (and (chaperone-multi->? new)
           (chaperone-multi->? old)
           chaperone-multi->)
      (and (impersonator-multi->? new)
           (impersonator-multi->? old)
           impersonator-multi->)))
