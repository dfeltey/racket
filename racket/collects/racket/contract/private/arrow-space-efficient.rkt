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

(provide val-has-arrow-space-efficient-support?
         arrow-space-efficient-guard
         add-arrow-space-efficient-wrapper
         ->-contract-has-space-efficient-support?
         build-s-e-arrow)
(module+ for-testing
  (provide multi->? multi->-doms multi->-rng))

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

;; contains all the information necessary to both (1) perform first order checks
;; for an arrow contract, and (2) determine which such checks are redundant and
;; can be eliminated
(struct arrow-first-order-check (n-doms blame missing-party method?))
;; stronger really means "the same" here
(define (arrow-first-order-check-stronger? x y)
  (= (arrow-first-order-check-n-doms x) (arrow-first-order-check-n-doms y)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Applicability checks

(define (->-contract-has-space-efficient-support? ctc)
  (define-syntax-rule (bail reason)
    (begin
      (log-space-efficient-contract-bailout-info (format "arrow: ~a" reason))
      #f))
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


;; FIXME: Need 2 versions of this function
(define (val-has-arrow-space-efficient-support? chap-not-imp? val)
  (define-syntax-rule (bail reason)
    (begin
      (log-space-efficient-value-bailout-info (format "arrow: ~a" reason))
      #f))
  (and (or (procedure? val)
           (bail "not a procedure"))
       ;; the interposition wrapper has to support a superset of the arity
       ;; of the function it's wrapping, and ours can't support optional
       ;; args, keywords, etc. so just bail out in these cases
       (or (integer? (procedure-arity val))
           (bail "has optional args"))
       (or (let-values ([(man opt) (procedure-keywords val)]) ; no keyword arguments
             (and (null? man) (null? opt)))
           (bail "has keyword args"))
       (or (equal? (procedure-result-arity val) 1)
           (bail "can't prove single-return-value"))

       ;; TODO: lift this out as safe-for-space-efficient 
       
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
       (or (cond
             [(has-impersonator-prop:checking-wrapper? val)
              (define checking-wrapper
                (get-impersonator-prop:checking-wrapper val))
              (equal? (chaperone? checking-wrapper)
                      chap-not-imp?)]
             [else #t])
           (bail "switching from imp to chap or vice versa"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Wrapper management and contract checking

;; (or/c contract? multi/c?) × α × boolean? → α
(define (arrow-space-efficient-guard s-e val neg-party)
  ;; TODO: sometimes the first-order checks are redundant ...
  (do-arrow-first-order-checks s-e val neg-party)
  (define chap-not-imp? (chaperone-multi->? s-e))
  (cond
    [(val-has-arrow-space-efficient-support? val chap-not-imp?)
     (add-arrow-space-efficient-wrapper s-e val neg-party chap-not-imp?)]
    [else (bail-to-regular-wrapper s-e val neg-party)]))

;; TODO: what should the name of this function be ....
(define (add-arrow-space-efficient-wrapper s-e val neg-party chap-not-imp?)
  (define-values (merged-s-e new-neg checking-wrapper)
    (cond
      [(has-impersonator-prop:checking-wrapper? val)
       (define s-e-prop (get-impersonator-prop:space-efficient val))
       (define-values (merged-s-e new-neg)
         ;; TODO: can this fail if we've got this far?
         ;; this is specialized because that makes sense in the current
         ;; implementation ...
         (arrow-try-merge s-e neg-party (car s-e-prop) (cdr s-e-prop)))
       (values merged-s-e
               new-neg
               (get-impersonator-prop:checking-wrapper val))]
      [else
       (values s-e neg-party (make-checking-wrapper val chap-not-imp?))]))
  (cond
    [merged-s-e
     (define chap/imp (if chap-not-imp? chaperone-procedure impersonate-procedure))
     (define blame (multi-ho/c-latest-blame merged-s-e))
     (define b (box #f))
     (define res
       (chap/imp
        checking-wrapper
        #f
        impersonator-prop:checking-wrapper checking-wrapper
        impersonator-prop:outer-wrapper-box b
        impersonator-prop:space-efficient (cons merged-s-e new-neg)
        impersonator-prop:contracted (multi-ho/c-latest-ctc merged-s-e)
        impersonator-prop:blame (blame-add-missing-party blame neg-party)))
     (set-box! b res)
     res]
    [else (bail-to-regular-wrapper s-e val neg-party)]))

(define (make-checking-wrapper unwrapped chap-not-imp?)
  (if chap-not-imp?
      (chaperone-procedure* unwrapped arrow-wrapper)
      (impersonate-procedure* unwrapped arrow-wrapper)))

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
(define-syntax (make-interposition-procedure stx)
  (syntax-case stx ()
    [(_ maybe-closed-over-m/c)
     ;; Note: it would be more efficient to have arity-specific wrappers here,
     ;;   as opposed to using a rest arg.
     #`(λ (outermost-chaperone . args)
         (define prop
           #,(if (syntax-e #'maybe-closed-over-m/c)
                 #'maybe-closed-over-m/c ; we did close over the contract
                 ;; otherwise, get it from the impersonator property
                 #'(get-impersonator-prop:space-efficient outermost-chaperone)))
         (define m/c (car prop))
         (define neg (or (multi-ho/c-missing-party m/c) (cdr prop)))
         (define doms   (multi->-doms         m/c))
         (define rng    (multi->-rng          m/c))
         (define blame  (blame-add-missing-party
                         (multi-ho/c-latest-blame m/c) ; latest is ok here
                         neg))
         (define n-args (length args))
         (define n-doms (length doms))
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
                 (space-efficient-guard rng result neg)))))
         (apply values
                rng-checker
                (for/list ([dom (in-list doms)]
                           [arg (in-list args)])
                  (with-space-efficient-contract-continuation-mark
                    (with-contract-continuation-mark
                      blame
                      (space-efficient-guard dom arg neg))))))]))

(define arrow-wrapper (make-interposition-procedure #f))

;; create a regular checking wrapper from a space-efficient wrapper for a value
;; that can't use space-efficient wrapping
(define (bail-to-regular-wrapper m/c val neg-party)
  (define chap-not-imp? (chaperone-multi->? m/c))
  (define neg (or (multi-ho/c-missing-party m/c) neg-party))
  ((if chap-not-imp? chaperone-procedure* impersonate-procedure*)
   val
   (make-interposition-procedure (cons m/c neg-party))
   impersonator-prop:contracted (multi-ho/c-latest-ctc   m/c)
   impersonator-prop:blame (blame-add-missing-party
                            (multi-ho/c-latest-blame m/c)
                            neg)
   impersonator-prop:space-efficient #f
   impersonator-prop:unwrapped val))

(define (do-arrow-first-order-checks m/c val neg-party)
  (define checks (multi->-first-order-checks m/c))
  (for ([c (in-list checks)])
    (define n-doms (arrow-first-order-check-n-doms c))
    (define partial-blame (arrow-first-order-check-blame c))
    (define neg (arrow-first-order-check-missing-party c))
    (define blame (blame-add-missing-party partial-blame (or neg neg-party)))
    (cond [(do-arity-checking
            blame
            val
            (for/list ([i (in-range n-doms)]) #f) ; has to have the right length
            #f ; no rest arg
            n-doms ; min-arity = max-arity
            '() ; no keywords
            (arrow-first-order-check-method? c))
           => (lambda (fail) (fail (or neg neg-party)))])))

(define (get-projection ctc)
  (lambda (val neg-party)
    (do-arrow-first-order-checks ctc val neg-party)
    (bail-to-regular-wrapper ctc val neg-party)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Space-efficient contract data structure management

;; Convert a higher-order contract to a multi-higher-order contract
;; Conversion consists of simultaneously copying the structure of the
;; higher-order contract and propagating the blame to the leaves.
;; At the leaves we convert contracts to multi-leaf/c
#;
(define (ho/c->multi-> ctc blame)
  (define chap-not-imp? (chaperone-contract? ctc))
  (define doms (base->-doms ctc))
  (define rng  (car (base->-rngs ctc))) ; assumes single range
  (define dom-blame (blame-swap blame))
  ((if chap-not-imp? chaperone-multi-> impersonator-multi->)
   blame
   ctc
   (for/vector ([dom (in-list doms)])
     (contract->space-efficient-contract dom dom-blame))
   (contract->space-efficient-contract rng blame)
   (list (arrow-first-order-check (length doms) blame (base->-method? ctc)))))

(define (build-s-e-arrow doms rng ctc blame chap?)
  (define focs
    (list (arrow-first-order-check (length doms) blame #f (base->-method? ctc))))
  (if chap?
      (chaperone-multi-> blame #f ctc doms rng focs)
      (impersonator-multi-> blame #f ctc doms rng focs)))

;; merge two multi->
(define (arrow-try-merge new-multi new-neg old-multi old-neg)
  (define constructor (get-constructor new-multi old-multi))
  (define merged
    (and constructor
         (constructor
          (multi-ho/c-latest-blame new-multi)
          (or (multi-ho/c-missing-party new-multi) new-neg)
          (multi-ho/c-latest-ctc   new-multi)
          ;; if old and new don't have the same arity, then one of them will *have*
          ;; to fail its first order checks, so we're fine.
          ;; (we don't support optional arguments)
          (for/list ([new (in-list (multi->-doms new-multi))]
                     [old (in-list (multi->-doms old-multi))])
            (define-values (merged _) (merge old old-neg new new-neg))
            merged)
          (let-values ([(merged _)
                        (merge (multi->-rng new-multi) new-neg (multi->-rng old-multi) old-neg)])
            merged)
          (first-order-check-join
           (add-f-o-neg-party (multi->-first-order-checks old-multi) old-neg)
           (add-f-o-neg-party (multi->-first-order-checks new-multi) new-neg)
           arrow-first-order-check-stronger?))))
  (values merged #f))

(define (add-f-o-neg-party focs neg-party)
  (for/list ([foc (in-list focs)])
    (define missing-party (arrow-first-order-check-missing-party foc))
    (struct-copy
     arrow-first-order-check
     foc
     [missing-party (or missing-party neg-party)])))

(define (get-constructor new old)
  (or (and (chaperone-multi->? new)
           (chaperone-multi->? old)
           chaperone-multi->)
      (and (impersonator-multi->? new)
           (impersonator-multi->? old)
           impersonator-multi->)))

;; TODO: add the other pieces of this property
(define (->-space-efficient-contract-property chap?)
  (build-space-efficient-contract-property
   #:try-merge arrow-try-merge
   #:space-efficient-guard arrow-space-efficient-guard
   #:get-projection get-projection))

(struct chaperone-multi-> multi-> ()
  #:property prop:space-efficient-contract (->-space-efficient-contract-property #t))
(struct impersonator-multi-> multi-> ()
  #:property prop:space-efficient-contract (->-space-efficient-contract-property #f))
