#lang racket/base
(require (for-syntax racket/base
                     "application-arity-checking.rkt"
                     "arr-util.rkt")
         "kwd-info-struct.rkt"
         "arity-checking.rkt"
         "blame.rkt"
         "misc.rkt"
         "prop.rkt"
         "guts.rkt"
         "generate.rkt"
         "arrow-higher-order.rkt"
         racket/stxparam
         (prefix-in arrow: "arrow.rkt")
         (only-in racket/function normalize-arity arity=?))

(provide ->2 ->*2
         (for-syntax ->2-handled?
                     ->*2-handled?
                     ->-valid-app-shapes
                     ->*-valid-app-shapes))

(define-for-syntax (->2-handled? stx)
  (syntax-case stx (any values any/c)
    [(_ args ...)
     (syntax-parameter-value #'arrow:making-a-method)
     #f]
    [(_ any/c ... any)
     ;; should turn into a flat contract
     #f]
    [_ #t]))

(define-for-syntax (->*2-handled? stx)
  (syntax-case stx (any values any/c)
    [(_ args ...)
     (syntax-parameter-value #'arrow:making-a-method)
     #f]
    [_ #t]))

(define-for-syntax popular-keys
  ;; of the 8417 contracts that get compiled during
  ;; 'raco setup' of the current tree, these are all
  ;; the ones that appear at least 50 times (the
  ;; number indicate how many times each appeared)
  `((0 0 () () #f 1)   ; 1260
    (0 0 () () #t 1)   ;   58
    (1 0 () () #f #f)  ;  116
    (1 0 () () #f 1)   ; 4140
    (1 0 () () #t 1)   ;   71
    (1 1 () () #f 1)   ;  186
    (1 2 () () #f 1)   ;  125
    (2 0 () () #f #f)  ;   99
    (2 0 () () #f 1)   ; 1345
    (2 1 () () #f 1)   ;   68
    (3 0 () () #f 1)   ;  423
    (4 0 () () #f 1)   ;  149
    (5 0 () () #f 1))) ;   74

(define-syntax (generate-popular-key-ids stx)
  #`(define-for-syntax #,(datum->syntax stx 'popular-key-ids)
      (list #,@(map (λ (x y) #`(list (quote-syntax #,x) (quote-syntax #,y)))
                    (generate-temporaries (for/list ([e (in-list popular-keys)])
                                            'popular-plus-one-key-id))
                    (generate-temporaries (for/list ([e (in-list popular-keys)])
                                            'popular-chaperone-key-id))))))
(generate-popular-key-ids)

(define-for-syntax (build-plus-one-arity-function+chaperone-constructor
                    stx
                    regular-args
                    optional-args
                    mandatory-kwds
                    optional-kwds
                    pre
                    rest
                    rngs
                    post)
  (define key (and (not pre)
                   (not post)
                   (list (length regular-args)
                         (length optional-args)
                         (map syntax-e mandatory-kwds)
                         (map syntax-e optional-kwds)
                         (and rest #t)
                         (and rngs (if (syntax? rngs)
                                       (length (syntax->list rngs))
                                       (length rngs))))))
  (cond
    [(and key (member key popular-keys))
     =>
     (λ (l)
       (define index (- (length popular-keys) (length l)))
       (define ids (list-ref popular-key-ids index))
       (values (list-ref ids 0) (list-ref ids 1)))]
    [else
     (values (build-plus-one-arity-function/real
              regular-args
              optional-args
              mandatory-kwds
              optional-kwds
              pre
              rest
              rngs
              post)
             (build-chaperone-constructor/real
              '() ;; this-args 
              regular-args
              optional-args
              mandatory-kwds
              optional-kwds
              pre
              rest
              rngs
              post))]))

(define-syntax (build-populars stx)
  #`(begin
      #,@(for/list ([ids (in-list popular-key-ids)]
                    [key (in-list popular-keys)])
           (define plus-one-id (list-ref ids 0))
           (define chaperone-id (list-ref ids 1))
           (define-values (regular-arg-count
                           optional-arg-count
                           mandatory-kwds
                           optional-kwds
                           rest
                           rngs)
             (apply values key))
           (define mans (for/list ([x (in-range regular-arg-count)])
                          (string->symbol (format "man~a" x))))
           (define opts (for/list ([x (in-range optional-arg-count)])
                          (string->symbol (format "opt~a" x))))
           (define rng-vars (and rngs (for/list ([x (in-range rngs)])
                                        (string->symbol (format "rng~a" x)))))
           #`(begin
               (define #,(syntax-local-introduce plus-one-id)
                 #,(build-plus-one-arity-function/real
                    mans opts
                    mandatory-kwds
                    optional-kwds
                    #f
                    rest
                    rng-vars
                    #f))
               (define #,(syntax-local-introduce chaperone-id)
                 #,(build-chaperone-constructor/real
                    '() ;; this arg
                    mans opts
                    mandatory-kwds
                    optional-kwds
                    #f
                    rest
                    rng-vars
                    #f))))))

(define-for-syntax (build-plus-one-arity-function/real
                    regular-args
                    optional-args
                    mandatory-kwds
                    optional-kwds
                    pre
                    rest
                    rngs
                    post)
  (with-syntax ([(regb ...) (generate-temporaries regular-args)]
                [(optb ...) (generate-temporaries optional-args)]
                [(kb ...) (generate-temporaries mandatory-kwds)]
                [(okb ...) (generate-temporaries optional-kwds)]
                [(rb ...) (generate-temporaries (or rngs '()))]
                [(arg-x ...) (generate-temporaries regular-args)]
                [(res-x ...) (generate-temporaries (or rngs '()))]
                [(kwd-arg-x ...) (generate-temporaries mandatory-kwds)])
    
    (with-syntax ([(formal-kwd-args ...)
                   (apply append (map list mandatory-kwds (syntax->list #'(kwd-arg-x ...))))]
                  [(kwd-arg-exps ...)
                   (apply append (map (λ (kwd kwd-arg-x kb) 
                                        (list kwd #`((#,kb #,kwd-arg-x) neg-party)))
                                      mandatory-kwds
                                      (syntax->list #'(kwd-arg-x ...))
                                      (syntax->list #'(kb ...))))]
                  [(letrec-bound-id) (generate-temporaries '(f))])
      
      (with-syntax ([(wrapper-args ...) #'(neg-party arg-x ... formal-kwd-args ...)]
                    [(the-call ...) #'(f ((regb arg-x) neg-party) ... kwd-arg-exps ...)]
                    [(pre-check ...)
                     (if pre 
                         (list #`(check-pre-condition blame neg-party f #,pre))
                         (list))]
                    [(post-check ...)
                     (if post
                         (list #`(check-post-condition blame neg-party f #,post))
                         (list))]
                    [(restb) (generate-temporaries '(rest-args))])
        (define body-proc
          (cond
            [(or (and (null? optional-args)
                      (null? optional-kwds))
                 (and (null? mandatory-kwds)
                      (null? optional-kwds)))
             (define case-lambda-clauses
               (let loop ([optional-args (reverse optional-args)]
                          [ob (reverse (syntax->list #'(optb ...)))]
                          [first? #t])
                 (define no-rest-call
                   #`(the-call ... #,@(for/list ([ob (in-list (reverse ob))]
                                                 [optional-arg (in-list (reverse optional-args))])
                                        #`((#,ob #,optional-arg) neg-party))))
                 (define full-call
                   (if (and first? rest)
                       #`(apply #,@no-rest-call ((restb rest-arg) neg-party))
                       no-rest-call))
                 (define the-args #`(wrapper-args ... 
                                     #,@(reverse optional-args)
                                     #,@(if (and first? rest)
                                            #'rest-arg
                                            '())))
                 (define the-clause
                   (if rngs
                       #`[#,the-args
                          pre-check ...
                          (define-values (failed res-x ...)
                            (call-with-values
                             (λ () #,full-call)
                             (case-lambda
                               [(res-x ...)
                                (values #f res-x ...)]
                               [args
                                (values args #,@(map (λ (x) #'#f) 
                                                     (syntax->list #'(res-x ...))))])))
                          (cond
                            [failed
                             (wrong-number-of-results-blame 
                              blame neg-party f
                              failed
                              #,(length 
                                 (syntax->list
                                  #'(res-x ...))))]
                            [else
                             post-check ...
                             (values ((rb res-x) neg-party) ...)])]
                       #`[#,the-args
                          pre-check ...
                          #,full-call]))
                 (cons the-clause
                       (cond
                         [(null? optional-args) '()]
                         [else (loop (cdr optional-args)
                                     (cdr ob)
                                     #f)]))))
             
             (cond
               [(null? (cdr case-lambda-clauses))
                ;; need to specialize this case because
                ;; there might be keyword arguments here
                #`(λ #,@(car case-lambda-clauses))]
               [else
                ;; (but there won't here)
                #`(case-lambda #,@case-lambda-clauses)])]
            [else
             #`(make-checking-proc f blame
                                   '(#,@mandatory-kwds) (list kb ...)
                                   '(#,@optional-kwds) (list okb ...) 
                                   #,(length regular-args) (list regb ... optb ...) 
                                   #,(if rest #'restb #'#f))]))
        #`(λ (blame f regb ... optb ... kb ... okb ... rb ... #,@(if rest (list #'restb) '()))
            #,body-proc)))))

(define (make-checking-proc f blame  
                            original-mandatory-kwds kbs
                            original-optional-kwds okbs
                            minimum-arg-count rbs rest-ctc)
  (make-keyword-procedure
   (λ (actual-kwds actual-kwd-args neg-party . regular-args)
     (check-arg-count minimum-arg-count rbs regular-args f blame neg-party rest-ctc)
     (check-keywords original-mandatory-kwds original-optional-kwds actual-kwds f blame neg-party)
     (keyword-apply
      f
      actual-kwds
      (let loop ([kwds actual-kwds]
                 [kwd-args actual-kwd-args]
                 [mandatory-kwds original-mandatory-kwds]
                 [optional-kwds original-optional-kwds]
                 [kbs kbs]
                 [okbs okbs])
        (cond
          [(null? kwd-args) '()]
          [else
           (define kwd (car kwds))
           (define kwd-arg (car kwd-args))
           (cond
             [(and (pair? mandatory-kwds)
                   (equal? (car mandatory-kwds) kwd))
              (cons (((car kbs) kwd-arg) neg-party)
                    (loop (cdr kwds) 
                          (cdr kwd-args)
                          (cdr mandatory-kwds)
                          optional-kwds
                          (cdr kbs)
                          okbs))]
             [(and (pair? optional-kwds)
                   (equal? (car optional-kwds) kwd))
              (cons (((car okbs) kwd-arg) neg-party)
                    (loop (cdr kwds) 
                          (cdr kwd-args)
                          mandatory-kwds
                          (cdr optional-kwds)
                          kbs
                          (cdr okbs)))]
             [(pair? optional-kwds)
              (loop kwds kwd-args mandatory-kwds (cdr optional-kwds) kbs (cdr okbs))]
             [else
              (error 'arrow-val-first.rkt
                     (string-append
                      "internal error:\n  f ~s\n  actual-kwds ~s"
                      "\n  mandatory-kwds ~s\n  optional-kwds ~s\n  neg-party ~s")
                     f actual-kwds original-mandatory-kwds original-optional-kwds neg-party)])]))
      (let loop ([regular-args regular-args]
                 [rbs rbs])
        (cond
          [(null? regular-args) '()]
          [(null? rbs) ((rest-ctc regular-args) neg-party)]
          [else
           (cons (((car rbs) (car regular-args)) neg-party)
                 (loop (cdr regular-args) (cdr rbs)))]))))))

(build-populars)

(define (check-arg-count minimum-arg-count rbs regular-args val blame neg-party rest-ctc)
  (define actual-count (length regular-args))
  (cond
    [(< actual-count minimum-arg-count)
     (raise-blame-error (blame-swap blame) #:missing-party neg-party val
                        '(expected: "~a~a arguments")
                        (if (= (length rbs) minimum-arg-count)
                            ""
                            "at least ")
                        minimum-arg-count)]
    [(and (not rest-ctc) (< (length rbs) actual-count))
     (raise-blame-error (blame-swap blame) #:missing-party neg-party val
                        '(expected: "~a~a arguments")
                        (if (= (length rbs) minimum-arg-count)
                            ""
                            "at most ")
                        (+ minimum-arg-count (length rbs)))]))

(define (check-keywords mandatory-kwds optional-kwds kwds val blame neg-party)
  (let loop ([mandatory-kwds mandatory-kwds]
             [optional-kwds optional-kwds]
             [kwds kwds])
    (cond
      [(null? kwds) 
       (unless (null? mandatory-kwds)
         (raise-blame-error (blame-swap blame) #:missing-party neg-party val
                            '(expected: "keyword argument ~a")
                            (car mandatory-kwds)))]
      [else
       (define kwd (car kwds))
       (cond
         [(and (null? optional-kwds) (null? mandatory-kwds))
          (raise-blame-error (blame-swap blame) #:missing-party neg-party val
                             '(expected: "no keyword argument ~a")
                             kwd)]
         [(and (pair? mandatory-kwds)
               (or (null? optional-kwds)
                   (keyword<? (car mandatory-kwds) (car optional-kwds))))
          (define man-kwd (car mandatory-kwds))
          (cond
            [(equal? kwd man-kwd)
             (loop (cdr mandatory-kwds) optional-kwds (cdr kwds))]
            [(keyword<? kwd man-kwd) 
             (raise-blame-error (blame-swap blame) #:missing-party neg-party val
                                '(expected: "no keyword argument ~a")
                                kwd)]
            [(keyword<? man-kwd kwd) 
             (raise-blame-error (blame-swap blame) #:missing-party neg-party val
                                '(expected: "keyword argument ~a")
                                man-kwd)])]
         [(and (pair? optional-kwds)
               (or (null? mandatory-kwds)
                   (keyword<? (car optional-kwds) (car mandatory-kwds))))
          (define opt-kwd (car optional-kwds))
          (cond
            [(equal? kwd opt-kwd)
             (loop mandatory-kwds (cdr optional-kwds) (cdr kwds))]
            [(keyword<? kwd opt-kwd)
             (raise-blame-error (blame-swap blame) #:missing-party neg-party val
                                '(expected: "no keyword argument ~a")
                                kwd)]
            [(keyword<? opt-kwd kwd)
             (loop mandatory-kwds (cdr optional-kwds) kwds)])])])))

                   
(define (check-pre-condition blame neg-party val thunk)
  (unless (thunk)
    (raise-blame-error
     (blame-swap blame) #:missing-party neg-party val
     "#:pre condition failure")))

(define (check-post-condition blame neg-party val thunk)
  (unless (thunk)
    (raise-blame-error
     blame #:missing-party neg-party val
     "#:post condition failure")))

(define-for-syntax (parse-arrow-args stx args this->)
  (let loop ([args args]
             [regular-args '()]
             [kwds '()]
             [kwd-args '()]
             [let-bindings '()])
    (cond
      [(null? args) 
       (define sorted
         (sort (map cons kwds kwd-args)
               keyword<?
               #:key (compose syntax-e car)))
       (values (reverse regular-args)
               (map car sorted)
               (map cdr sorted)
               let-bindings)]
      [else
       (with-syntax ([(arg-x) (generate-temporaries (list (car args)))])
         (syntax-case (car args) ()
           [kwd
            (keyword? (syntax-e #'kwd))
            (begin
              (when (null? (cdr args))
                (raise-syntax-error '-> 
                                    "expected a contract to follow the keyword (plus the range)"
                                    stx
                                    (car args)))
              (loop (cddr args)
                    regular-args
                    (cons (car args) kwds)
                    (cons #'arg-x kwd-args)
                    (cons #`[arg-x #,(syntax-property (cadr args) 
                                                      'racket/contract:negative-position 
                                                      this->)]
                          let-bindings)))]
           [else
            (loop (cdr args)
                  (cons #'arg-x regular-args)
                  kwds
                  kwd-args
                  (cons #`[arg-x #,(syntax-property (car args) 
                                                    'racket/contract:negative-position 
                                                    this->)]
                        let-bindings))]))])))

(define-for-syntax (->-valid-app-shapes stx)
  (syntax-case stx ()
    [(_ args ...)
     (let ()
       (define this-> (gensym 'this->))
       (define-values (regular-args kwds kwd-args let-bindings)
         (parse-arrow-args stx (syntax->list #'(args ...)) this->))
       (valid-app-shapes (list (- (length regular-args) 1))
                         (map syntax->datum kwds)
                         '()))]))

(define-syntax (->2 stx)
  (syntax-case stx ()
    [(_ args ...)
     (not (->2-handled? stx))
     #'(arrow:-> args ...)]
    [(_ args ... rng)
     (let ()
       (define this-> (gensym 'this->))
       (define-values (regular-args kwds kwd-args let-bindings)
         (parse-arrow-args stx (syntax->list #'(args ...)) this->))
       (define (add-pos-obligations stxes)
         (for/list ([stx (in-list stxes)])
           (syntax-property stx 'racket/contract:positive-position this->)))
       (define rngs
         (syntax-case #'rng (any values)
           [any #f]
           [(values rng ...) (add-pos-obligations (syntax->list #'(rng ...)))]
           [rng (add-pos-obligations (list #'rng))]))
       (define-values (plus-one-arity-function chaperone-constructor)
         (build-plus-one-arity-function+chaperone-constructor 
          stx regular-args '() kwds '() #f #f rngs #f))
       (syntax-property
        #`(let #,let-bindings
            #,(quasisyntax/loc stx
                (build-simple-->
                 (list #,@regular-args)
                 '(#,@kwds)
                 (list #,@kwd-args)
                 #,(if rngs
                       #`(list #,@rngs)
                       #'#f)
                 #,plus-one-arity-function
                 #,chaperone-constructor)))
        'racket/contract:contract
        (vector this->
                ;; the -> in the original input to this guy
                (list (car (syntax-e stx)))
                '())))]))

;; not quite the same as split-doms in arr-util.rkt, but similar idea.
(define-for-syntax (:split-doms stx name raw-doms)
  (let loop ([raw-doms raw-doms]
             [doms '()]
             [kwd-doms '()]
             [let-bindings '()])
    (syntax-case raw-doms ()
      [() (list (reverse doms)
                (sort-keywords stx kwd-doms)
                (reverse let-bindings))]
      [(kwd arg . rest)
       (and (keyword? (syntax-e #'kwd))
            (not (keyword? (syntax-e #'arg))))
       (with-syntax ([(x) (generate-temporaries #'(kwd))])
         (loop #'rest
               doms
               (cons #'(kwd x) kwd-doms)
               (cons #`[x arg] let-bindings)))]
      [(kwd arg . rest)
       (and (keyword? (syntax-e #'kwd))
            (keyword? (syntax-e #'arg)))
       (raise-syntax-error name
                           "cannot have two keywords in a row"
                           stx
                           #'kwd)]
      [(kwd)
       (keyword? (syntax-e #'kwd))
       (raise-syntax-error name
                           "cannot have a keyword at the end"
                           stx
                           #'kwd)]
      [(x . rest)
       (with-syntax ([(t) (generate-temporaries #'(x))])
         (loop #'rest 
               (cons #'t doms) 
               kwd-doms
               (cons #`[t x] let-bindings)))])))

(define-for-syntax (parse->*2 stx)
  (syntax-case stx ()
    [(_ (raw-mandatory-dom ...) . other)
     (let ()
       (define-values (raw-optional-doms rest-ctc pre rng-ctcs post)
         (arrow:parse-leftover->* stx #'other))
       (with-syntax ([(man-dom
                       man-dom-kwds
                       man-lets)
                      (:split-doms stx '->* #'(raw-mandatory-dom ...))]
                     [(opt-dom
                       opt-dom-kwds
                       opt-lets)
                      (:split-doms stx '->* raw-optional-doms)])
         (values
          #'man-dom
          #'man-dom-kwds
          #'man-lets
          #'opt-dom
          #'opt-dom-kwds
          #'opt-lets
          rest-ctc pre rng-ctcs post)))]))

(define-for-syntax (->*-valid-app-shapes stx)
  (define-values (man-dom man-dom-kwds man-lets
                          opt-dom opt-dom-kwds opt-lets
                          rest-ctc pre rng-ctcs post)
    (parse->*2 stx))
  (with-syntax ([((mandatory-dom-kwd mandatory-dom-kwd-ctc) ...) man-dom-kwds]
                [((optional-dom-kwd optional-dom-kwd-ctc) ...) opt-dom-kwds])
    (valid-app-shapes-from-man/opts (length (syntax->list man-dom))
                                    (length (syntax->list opt-dom))
                                    rest-ctc
                                    (syntax->datum #'(mandatory-dom-kwd ...))
                                    (syntax->datum #'(optional-dom-kwd ...)))))

(define-syntax (->*2 stx)
  (cond
    [(->*2-handled? stx)
     (define-values (man-dom man-dom-kwds man-lets
                             opt-dom opt-dom-kwds opt-lets
                             rest-ctc pre rng-ctcs post)
       (parse->*2 stx))
     (with-syntax ([(mandatory-dom ...) man-dom]
                   [((mandatory-dom-kwd mandatory-dom-kwd-ctc) ...) man-dom-kwds]
                   [(mandatory-let-bindings ...) man-lets]
                   [(optional-dom ...) opt-dom]
                   [((optional-dom-kwd optional-dom-kwd-ctc) ...) opt-dom-kwds]
                   [(optional-let-bindings ...) opt-lets]
                   [(pre-x post-x) (generate-temporaries '(pre-cond post-cond))])
       (with-syntax ([((kwd dom opt?) ...) #'((mandatory-dom-kwd mandatory-dom-kwd-ctc #f) ...
                                              (optional-dom-kwd optional-dom-kwd-ctc #t) ...)]
                     [(pre-let-binding ...) (if pre
                                                (list #`[pre-x (λ () #,pre)])
                                                (list))]
                     [(post-let-binding ...) (if post
                                                 (list #`[post-x (λ () #,post)])
                                                 (list))])
         (define-values (plus-one-arity-function chaperone-constructor)
           (build-plus-one-arity-function+chaperone-constructor
            stx
            (syntax->list #'(mandatory-dom ...))
            (syntax->list #'(optional-dom ...))
            (syntax->list #'(mandatory-dom-kwd ...))
            (syntax->list #'(optional-dom-kwd ...))
            (and pre #'pre-x)
            rest-ctc
            rng-ctcs
            (and post #'post-x)))
         #`(let (mandatory-let-bindings ...
                 optional-let-bindings ... 
                 pre-let-binding ...
                 post-let-binding ...)
             (build--> '->*
                       (list mandatory-dom ...)
                       (list optional-dom ...)
                       '(mandatory-dom-kwd ...)
                       (list mandatory-dom-kwd-ctc ...)
                       '(optional-dom-kwd ...)
                       (list optional-dom-kwd-ctc ...)
                       #,rest-ctc
                       #,(and pre #t)
                       #,(if rng-ctcs
                             #`(list #,@rng-ctcs)
                             #'#f)
                       #,(and post #t)
                       #,plus-one-arity-function 
                       #,chaperone-constructor))))]
    [else
     (syntax-case stx ()
       [(_ args ...)
        #'(arrow:->* args ...)])]))

(define (wrong-number-of-results-blame blame neg-party val reses expected-values)
  (define length-reses (length reses))
  (raise-blame-error 
   blame #:missing-party neg-party val
   '("received ~a value~a" expected: "~a value~a")
   length-reses
   (if (= 1 length-reses) "" "s")
   expected-values
   (if (= 1 expected-values) "" "s")))

(define (build-simple--> raw-regular-doms
                         mandatory-kwds mandatory-raw-kwd-doms
                         raw-rngs
                         plus-one-arity-function
                         chaperone-constructor)
  (build--> '->
            raw-regular-doms '() 
            mandatory-kwds mandatory-raw-kwd-doms
            '() '()
            #f
            #f raw-rngs #f
            plus-one-arity-function
            chaperone-constructor))

(define (build--> who 
                  raw-regular-doms raw-optional-doms 
                  mandatory-kwds mandatory-raw-kwd-doms
                  optional-kwds optional-raw-kwd-doms
                  raw-rest-ctc
                  pre-cond raw-rngs post-cond
                  plus-one-arity-function
                  chaperone-constructor)
  (define regular-doms
    (for/list ([dom (in-list (append raw-regular-doms raw-optional-doms))])
      (coerce-contract who dom)))
  (define mandatory-kwd-infos 
    (for/list ([kwd (in-list mandatory-kwds)]
               [dom (in-list mandatory-raw-kwd-doms)])
      (kwd-info kwd (coerce-contract who dom) #t)))
  (define optional-kwd-infos 
    (for/list ([kwd (in-list optional-kwds)]
               [dom (in-list optional-raw-kwd-doms)])
      (kwd-info kwd (coerce-contract who dom) #f)))
  (define kwd-infos (sort (append optional-kwd-infos mandatory-kwd-infos)
                          keyword<?
                          #:key kwd-info-kwd))
  (define rest-ctc (and raw-rest-ctc (coerce-contract who raw-rest-ctc)))
  (define rngs
    (and raw-rngs
         (for/list ([rng (in-list raw-rngs)])
           (coerce-contract who rng))))
  (if (and (andmap chaperone-contract? regular-doms)
           (andmap (λ (x) (chaperone-contract? (kwd-info-ctc x))) kwd-infos)
           (andmap chaperone-contract? (or rngs '())))
      (make--> (length raw-regular-doms) 
               regular-doms kwd-infos rest-ctc pre-cond
               rngs post-cond 
               plus-one-arity-function
               chaperone-constructor)
      (make-impersonator-> (length raw-regular-doms)
                           regular-doms kwd-infos rest-ctc pre-cond
                           rngs post-cond 
                           plus-one-arity-function
                           chaperone-constructor)))

;; min-arity : nat
;; doms : (listof contract?)[len >= min-arity]
;;        includes optional arguments in list @ end
;; kwd-infos : (listof kwd-info)
;; rest : (or/c #f contract?)
;; pre? : boolean?
;; rngs : (listof contract?)
;; post? : boolean?
;; plus-one-arity-function : procedure? -- special, +1 argument wrapper that accepts neg-party
;; chaperone-constructor ; procedure? -- function that builds a projection tailored to this arrow
(define-struct base-> (min-arity doms kwd-infos rest pre? rngs post?
                                 plus-one-arity-function chaperone-constructor)
  #:property prop:custom-write custom-write-property-proc)

(define (->-generate ctc)
  ;; local definitions to remove racket/list dependencies
  (define (filter-not pred lst) (filter (lambda (v) (not (pred v))) lst))
  (define (split lst n)
    (let-values ([(rf b) (for/fold ([front null]
                                    [back lst])
                           ([i n])
                           (if (null? back)
                               (values front back)
                               (values (cons (car back) front) (cdr back))))])
      (values (reverse rf) b))) 
  (define min-arity (base->-min-arity ctc))
  (define doms (base->-doms ctc))
  (define kwd-infos (base->-kwd-infos ctc))
  (define rest-ctc (base->-rest ctc))
  (define rng-ctcs (base->-rngs ctc))
  ;; printing ranges to see what any, any/c look like in contracts
  ;(printf "doms: ~a\n" doms)
  ;(printf "ranges: ~a\n" rng-ctcs)
  
  
  ;; build proper function arity
  (define arity (normalize-arity 
                 (if rest-ctc  
                     (arity-at-least min-arity)
                     (build-list (add1 (- (length doms) min-arity))
                                 (lambda (n) (+ n min-arity))))))
  ;; get the required kwd-infos 
  (define req-kwd-infos (filter kwd-info-mandatory? kwd-infos))
  
  ;; define and sort the lists of keywords
  (define required-kws (sort (map kwd-info-kwd req-kwd-infos) keyword<?))
  (define allowed-kws (sort (map kwd-info-kwd kwd-infos) keyword<?))
  
  ;; hash mapping keywords to their contracts
  (define kwd-ctc-hash 
    (make-hash (map (lambda (ki) (cons (kwd-info-kwd ki) (kwd-info-ctc ki))) kwd-infos)))
  
  ;; split the domain contracts into a list of required positional ctc 
  ;; amd optional positional ctcs
  (define-values (req-pos-ctcs opt-pos-ctcs)
    (split doms min-arity))
  
  ;; get the max number of optional arguments
  (define max-opt-arity (length opt-pos-ctcs)) 
  
  ;; result of ->-generate
  (λ (fuel)
    ;; TODO: rng-ctcs can be #f in the case of (-> ... any)
    ;; and any/c cannot be generated right now 
    (define rngs-gens (map (λ (c) (generate/choose c (/ fuel 2))) rng-ctcs))
    (cond
      [(for/or ([rng-gen (in-list rngs-gens)])
         (generate-ctc-fail? rng-gen))
       (make-generate-ctc-fail)]
      [else
       (procedure-reduce-keyword-arity
        (make-keyword-procedure
         (lambda (kws kw-args . pos+rest-args)
           ;; Check keyword arguments
           (for ([kw kws]
                 [kw-arg kw-args])
             ;; still need to handle contract-exercise in a better way
             (unless ((contract-struct-exercise (hash-ref kwd-ctc-hash kw)) kw-arg (/ fuel 2))
               (raise-arguments-error '->-generated-function 
                                      "contract violation"
                                      "expected" (contract-name (hash-ref kwd-ctc-hash kw))
                                      "given" kw-arg
                                      "in" (format "the ~a argument of\n ~a" kw (contract-name ctc)))))
           
           ;; split pos+rest-args into required positional arguments and optional+rest arguments
           (define-values (req-pos-args opt+rest-args) (split pos+rest-args min-arity))
           
           ;; split the opt+rest-args into optional args and rest arg list
           (define-values (opt-pos-args rest) (split opt+rest-args max-opt-arity))
           
           ;; check required positional arguments
           (for ([pos-arg req-pos-args]
                 [pos-ctc req-pos-ctcs]
                 [i min-arity])
             (unless ((contract-struct-exercise pos-ctc) pos-arg (/ fuel 2))
               (raise-arguments-error '->generated-function
                                      "contract violation"
                                      "expected" (contract-name pos-ctc)
                                      "given" pos-arg
                                      "in" (format "argument ~a of ~a" (add1 i) (contract-name ctc)))))
           
           ;; check optional positional arguments
           (for ([opt-arg opt-pos-args]
                 [opt-ctc opt-pos-ctcs]
                 [i max-opt-arity])
             (unless ((contract-struct-exercise opt-ctc) opt-arg (/ fuel 2))
               (raise-arguments-error '->generated-function
                                      "contract violation"
                                      "expected" (contract-name opt-ctc)
                                      "given" opt-arg
                                      "in" (format "optional argument ~a of ~a" (add1 i) (contract-name ctc)))))
           
          
           ;; check rest args
           ;; This is broken right now, but only because exercising for lists has not been implemented
           (unless (or (not rest-ctc) ((contract-struct-exercise rest-ctc) rest (/ fuel 2)))
             (raise-arguments-error '->generated-function
                                    "contract violation"
                                    "expected" (contract-name rest-ctc)
                                    "given" rest
                                    "in" (format "the rest argument of ~a"(contract-name ctc))))
           (apply values rngs-gens)))
        arity
        required-kws
        allowed-kws)])))

;; There are two possible approaches to exercising function contracts.
;; 1. Generate values for all arguments (including all optional and rest)
;;    then apply the function and check that the results are correct
;; 2. Generate all required arguments then randomly generate
;;    SOME, but not all of the optional keyword/positional arguments
;;    and only generate rest if all optional arguments were generated
;;
;; For testing, option 2 is probably better than 1 if the tests are run 
;; many times, a best (but difficult) third option is to exercise all the possible
;; combinations...
;;
;; For now taking approach 1 to avoid some difficult in generating
;; random subsequences or initial sections of a list.
;;
;; maybe shouldn't raise exceptions here... just display an error and 
;; return #f ..?
(define (->-exercise ctc) 
  ;; returns a function that checks if it's argument satisfies ctc
  (λ (arg fuel)
    (unless (procedure? arg)
      (raise-argument-error '->-exercise
                            "procedure?"
                            arg))
    
    (define min-arity (base->-min-arity ctc))
    (define doms (base->-doms ctc))
    (define kwd-infos (base->-kwd-infos ctc))
    (define rest-ctc (base->-rest ctc))
    (define rng-ctcs (base->-rngs ctc))
    
    ;; build contract arity
    (define ctc-arity (normalize-arity
                       (if rest-ctc  
                           (arity-at-least min-arity)
                           (build-list (add1 (- (length doms) min-arity))
                                       (lambda (n) (+ n min-arity))))))
    (define arg-arity (procedure-arity arg))
    
    ;; arity of ctc and arg should match
    (unless (arity=? ctc-arity arg-arity)
      (raise-arguments-error '->exercise
                             "arity mismatch between contract and given"
                             "expected arity" ctc-arity
                             "given arity" arg-arity))
    
    ;; get the required kwd-infos 
    (define req-kwd-infos (filter kwd-info-mandatory? kwd-infos))
    
    ;; define and sort the lists of keywords
    (define ctc-required-kws (sort (map kwd-info-kwd req-kwd-infos) keyword<?))
    (define ctc-allowed-kws (sort (map kwd-info-kwd kwd-infos) keyword<?))
    
    ;; get arg keywords
    (define-values (arg-required-kws arg-allowed-kws) (procedure-keywords arg))
    
    ;; make sure arg and ctc accept the same optional and required keywords
    (unless (and (equal? ctc-required-kws arg-required-kws)
                 (equal? ctc-allowed-kws arg-allowed-kws))
      (raise-arguments-error '->exercise 
                             "keyword argument mismatch between contract and given"
                             "expected required keywords" ctc-required-kws
                             "given required keywords" arg-required-kws
                             "expected allowed keywords" ctc-allowed-kws
                             "given allowed keywords" arg-allowed-kws))
    
    ;; now generate random arguments to apply arg to
    (define positional-args (map (λ (c) (contract-random-generate c (/ fuel 2))) doms))     
    
    (define kwd-args
      (let* ([kwd-ctcs (map (lambda (ki) (cons (kwd-info-kwd ki) (kwd-info-ctc ki))) kwd-infos)]
             [sorted-kwd-ctcs (sort kwd-ctcs (lambda (kc1 kc2) (keyword<? (car kc1) (car kc2))))])
        (map (lambda (kc) (contract-random-generate (cdr kc) (/ fuel 2))) sorted-kwd-ctcs)))
    
    (define rest-args (if rest-ctc
                          (contract-random-generate rest-ctc (/ fuel 2))
                          null))
    ;; bundle arguments in a list for keyword-apply
    (define args-for-apply (append positional-args rest-args))
    ;; call arg on generated arguments, store results in a list
    
    ;; this could possible throw a contract error or something else, should probably
    ;; be wrapped in with-handlers
    (define results
      (call-with-values (lambda () (keyword-apply arg ctc-allowed-kws kwd-args args-for-apply))
                        list))
    ;; ignore checking if rng-ctcs was false, otherwise check length 
    (cond
      [(not rng-ctcs) #t] ; no checking, just return true
      [(not (= (length rng-ctcs) 
               (length results)))
       (raise-arguments-error '->-exercise
                              "received incorrect number of result values"
                              "expected" (length rng-ctcs)
                              "received" (length results)
                              "results" results)]
      [else 
       (for ([result results]
             [ctc rng-ctcs])
         (unless ((contract-struct-exercise ctc) result (/ fuel 2))
           (raise-result-error '->-exercise
                               (format "~a" ctc)
                               result)))
       ;; this isn't quite right, need to fix dealing with exceptions ...
       #t]))
  
  #;(λ (args fuel)
    (let* ([new-fuel (/ fuel 2)]
           [gen-if-fun (λ (c v)
                         ; If v is a function we need to gen the domain and call
                         (if (procedure? v)
                             (let ([newargs (map (λ (c) (contract-random-generate c new-fuel))
                                                 (base->-doms c))])
                               (let* ([result (call-with-values 
                                               (λ () (apply v newargs))
                                               list)]
                                      [rngs (base->-rngs c)])
                                 (andmap (λ (c v) 
                                           ((contract-struct-exercise c) v new-fuel))
                                         rngs 
                                         result)))
                             ; Delegate to check-ctc-val
                             ((contract-struct-exercise c) v new-fuel)))])
      (andmap gen-if-fun (base->-doms ctc) args))))

(define (base->-name ctc)
  (define rngs (base->-rngs ctc))
  (define rng-sexp
    (cond
      [(not rngs) 'any]
      [(= 1 (length rngs))
       (contract-name (car rngs))]
      [else
       `(values ,@(map contract-name rngs))]))
  (cond
    [(and (andmap kwd-info-mandatory? (base->-kwd-infos ctc))
          (= (base->-min-arity ctc)
             (length (base->-doms ctc)))
          (not (base->-rest ctc))
          (not (base->-pre? ctc))
          (not (base->-post? ctc)))
     `(-> ,@(map contract-name (base->-doms ctc))
          ,@(apply
             append
             (for/list ([kwd-info (base->-kwd-infos ctc)])
               (list (kwd-info-kwd kwd-info) 
                     (contract-name (kwd-info-ctc kwd-info)))))
          ,rng-sexp)]
    [else
     (define (take l n) (reverse (list-tail (reverse l) (- (length l) n))))
     (define mandatory-args
       `(,@(map contract-name (take (base->-doms ctc) (base->-min-arity ctc)))
         ,@(apply
            append
            (for/list ([kwd-info (base->-kwd-infos ctc)]
                       #:when (kwd-info-mandatory? kwd-info))
              (list (kwd-info-kwd kwd-info) 
                    (contract-name (kwd-info-ctc kwd-info)))))))
     
     (define optional-args
       `(,@(map contract-name (list-tail (base->-doms ctc) (base->-min-arity ctc)))
         ,@(apply
            append
            (for/list ([kwd-info (base->-kwd-infos ctc)]
                       #:when (not (kwd-info-mandatory? kwd-info)))
              (list (kwd-info-kwd kwd-info) 
                    (contract-name (kwd-info-ctc kwd-info)))))))
     
     `(->* ,mandatory-args 
           ,@(if (null? optional-args)
                 '()
                 (list optional-args))
           ,@(if (base->-rest ctc)
                 (list '#:rest (contract-name (base->-rest ctc)))
                 (list))
           ,@(if (base->-pre? ctc)
                 (list '#:pre '...)
                 (list))
           ,rng-sexp
           ,@(if (base->-post? ctc)
                 (list '#:post '...)
                 (list)))]))

(define ((->-first-order ctc) x)
  (define l (base->-min-arity ctc))
  (define man-kwds (for/list ([kwd-info (base->-kwd-infos ctc)]
                              #:when (kwd-info-mandatory? kwd-info))
                     (kwd-info-kwd kwd-info)))
  (define opt-kwds (for/list ([kwd-info (base->-kwd-infos ctc)]
                              #:unless (kwd-info-mandatory? kwd-info))
                     (kwd-info-kwd kwd-info)))
  (and (procedure? x) 
       (if (base->-rest ctc)
           (arrow:procedure-accepts-and-more? x l)
           (procedure-arity-includes? x l #t))
       (arrow:keywords-match man-kwds opt-kwds x)
       #t))

(define (make-property build-X-property chaperone-or-impersonate-procedure)
  (define proj 
    (λ (->stct)
      (->-proj chaperone-or-impersonate-procedure ->stct
               (base->-min-arity ->stct)
               (base->-doms ->stct)
               (base->-kwd-infos ->stct)
               (base->-rest ->stct)
               (base->-pre? ->stct)
               (base->-rngs ->stct)
               (base->-post? ->stct)
               (base->-plus-one-arity-function ->stct)
               (base->-chaperone-constructor ->stct))))
  (parameterize ([skip-projection-wrapper? #t])
    (build-X-property
     #:name base->-name 
     #:first-order ->-first-order
     #:projection
     (λ (this)
       (define cthis (proj this))
       (λ (blame)
         (define cblame (cthis blame))
         (λ (val)
           ((cblame val) #f))))
     #:stronger
     (λ (this that) 
       (and (base->? that)
            (= (length (base->-doms that))
               (length (base->-doms this)))
            (= (base->-min-arity this) (base->-min-arity that))
            (andmap contract-stronger? (base->-doms that) (base->-doms this))
            (= (length (base->-kwd-infos this))
               (length (base->-kwd-infos that)))
            (for/and ([this-kwd-info (base->-kwd-infos this)]
                      [that-kwd-info (base->-kwd-infos that)])
              (and (equal? (kwd-info-kwd this-kwd-info)
                           (kwd-info-kwd that-kwd-info))
                   (contract-stronger? (kwd-info-ctc that-kwd-info)
                                       (kwd-info-ctc this-kwd-info))))
            (if (base->-rngs this)
                (and (base->-rngs that)
                     (andmap contract-stronger? (base->-rngs this) (base->-rngs that)))
                (not (base->-rngs that)))
            (not (base->-pre? this))
            (not (base->-pre? that))
            (not (base->-post? this))
            (not (base->-post? that))))
     #:generate ->-generate
     #:exercise ->-exercise
     #:val-first-projection proj)))

(define-struct (-> base->) ()
  #:property
  prop:chaperone-contract
  (make-property build-chaperone-contract-property chaperone-procedure))

(define-struct (impersonator-> base->) ()
  #:property
  prop:contract
  (make-property build-contract-property impersonate-procedure))
