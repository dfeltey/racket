#lang racket/base
(require "test-util.rkt")

(parameterize ([current-contract-namespace
                (make-basic-contract-namespace
                 'racket/contract)])
  
  (contract-eval '(define ctc (vectorof integer?)))
  (contract-eval '(define (wrap x) (contract ctc x 'pos 'neg)))
  (contract-eval '(define vecof-one (wrap (wrap (vector 1)))))
  (contract-eval '(define bad-vecof-int (wrap (wrap (vector 'bad)))))

  (test/spec-passed
   'vec-space-efficient1
   '(vector-ref vecof-one 0))
  (test/spec-passed
   'vec-space-efficient2
   '(vector-set! vecof-one 0 2))
  (test/spec-failed
   'vec-space-efficient3
   '(vector-set! vecof-one 0 'nan)
   'neg)
  (test/spec-failed
   'vec-space-efficient4
   '(vector-ref bad-vecof-int 0)
   'pos)

  (test/spec-failed
   'vecof-bail-not-a-vector
   '(let* ([ctc (vectorof (vectorof integer?))]
           [v (contract ctc (contract ctc (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0))
   "inner-pos")

  (test/spec-failed
   'vec/c-bail-not-a-vector
   '(let* ([ctc (vector/c (vector/c integer?))]
           [v (contract ctc (contract ctc (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0))
   "inner-pos")

  (test/spec-failed
   'vec/c-different-lengths1
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c integer? integer?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0))
   "inner-pos")

  (test/spec-failed
   'vec/c-different-lengths2
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c integer? integer?)]
           [v (contract ctc2 (contract ctc1 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0))
   'pos)

  (test/spec-failed
   'vec/c-different-lengths3
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c integer? integer?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-set! v 0 7))
   "inner-pos")

  (test/spec-failed
   'vec/c-different-lengths4
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c integer? integer?)]
           [v (contract ctc2 (contract ctc1 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-set! v 0 7))
   'pos)

  ;; Testing basic keyword arguments
  ;; ***********************************************

  ;; If the flat? argument is #t, then the resulting contract is a flat contract, and the c argument must also be a flat contract.
  ;; Such flat contracts will be unsound if applied to mutable vectors, as they will not check future operations on the vector.
  (test/spec-passed 
	'vec-space-efficient-flat-passed
	'(let* ([ctc 	(vectorof integer? #:flat? #t)]
                [v 	(contract 
                   		ctc 
				(make-vector 10 42) 'pos 'neg )])
	(vector-ref v 1)))

  (test/spec-failed
        'vec-space-efficient-flat-failed!
        '(let* ([ctc    (vectorof integer? #:flat? #t)]
                [v      (contract 
                                ctc 
                                (make-vector 10 "42") 'pos 'neg )])
        'oeps)
	"pos")

  ;;Should pass the test because we indicate that it is a flat contract
  (test/spec-passed
	'vec-space-efficient-flat-set!
	'(let* ([ctc 	(vectorof integer? #:flat? #t)]
                [v 	(contract 
                   		ctc 
				(make-vector 10 42) 'pos 'neg )])
	(vector-set! v 1 "24")))

  ;If the immutable argument is #t and the c argument is a flat contract and the eager argument is #t, the result will be a flat contract. 
  (contract-eval  '(define ctc-flat (vectorof integer? #:immutable #t #:eager #t)))
  (test-true 'is-flat '(flat-contract? ctc-flat))

  (test/spec-failed
	'vec-space-efficient-flat-set!
	'(let* ([ctc 	(vectorof integer? #:immutable #t #:eager #t)]
                [v 	(contract 
                   		ctc 
				(make-vector 10 42) 'pos 'neg )])
	'should-fail)
	"pos")

  (test/spec-passed
	'vec-space-efficient-flat-set!
	'(let* ([ctc 	(vectorof integer? #:immutable #t #:eager #t)]
                [v 	(contract 
                   		ctc 
				(vector-immutable 10 42) 'pos 'neg )])
	(vector-ref v 1)))

   ;If the c argument is a chaperone contract, then the result will be a chaperone contract.
   (contract-eval '(define ctc-chap (vectorof (-> integer? integer?) #:immutable #t #:eager #t )))
   (test-true 'is-chaperone '(chaperone-contract? ctc-chap))


  (test/spec-passed
        'vec-space-efficient-vector-chap
        '(let* ([ctc-chap    (vectorof (-> integer? integer?) #:immutable #t #:eager #t)]
                [v      (contract 
                                ctc-chap 
                                (vector-immutable (lambda (x) x)  (lambda (x) (* x x))) 'pos 'neg )])
        ((vector-ref v 1) 10)))

   (test/spec-failed
        'vec-space-efficient-vector-chap-fail
        '(let* ([ctc-chap    (vectorof (-> integer? integer?) #:immutable #t #:eager #t)]
                [v      (contract 
                                ctc-chap 
                                (vector-immutable (lambda (x) "42")) 'pos 'neg )])
        ((vector-ref v 0) 10))
	"pos")
   
 
	
  ;; End basic keyword arguments
  ;; ***********************************************


  ;; non-flat contracts at the leaves/nested vectorof contracts
  (test/spec-passed
   'vec-space-efficient5
   '(let* ([ctc (vectorof (vectorof integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 0) (vector 1) (vector 2)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 1) 0)))

  (test/spec-failed
   'vec-space-efficient6a
   '(let* ([ctc (vectorof (vectorof integer?))]
           [v (contract ctc (vector (vector 'bad)) 'inner-pos 'inner-neg)])
      (vector-ref (vector-ref v 0) 0))
   "inner-pos")
  
  (test/spec-failed
   'vec-space-efficient6b
   '(let* ([ctc (vectorof (vectorof integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 'bad)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 0) 0))
   "inner-pos")

  (test/spec-failed
   'vec-space-efficient7
   '(let* ([ctc (vectorof (vectorof integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! (vector-ref v 0) 0 'bad))
   'neg)

  (test/spec-failed
   'vec-space-efficient8
   '(let* ([ctc (vectorof (vectorof integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! v 0 (vector 'bad))
      (vector-ref (vector-ref v 0) 0))
   'neg)

  ;; non-identical contracts in nested vectorof
  (test/spec-failed
   'vec-space-efficient9
   '(let* ([ctc1 (vectorof (vectorof integer?))]
           [ctc2 (vectorof (vectorof positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! (vector-ref v 0) 0 -1))
   "inner-neg")

  (test/spec-failed
   'vec-space-efficient10
   '(let* ([ctc1 (vectorof (vectorof integer?))]
           [ctc2 (vectorof (vectorof positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! (vector-ref v 0) 0 1/2))
   'neg)

  (test/spec-failed
   'vec-space-efficient11
   '(let* ([ctc1 (vectorof (vectorof integer?))]
           [ctc2 (vectorof (vectorof positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1/2)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 0) 0))
   'pos)

  (test/spec-failed
   'vec-space-efficient12
   '(let* ([ctc1 (vectorof (vectorof integer?))]
           [ctc2 (vectorof (vectorof positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector -1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 0) 0))
   "inner-pos")

  ;; tests for various first-order checks performed by vectors
  (test/spec-failed
   'vec-space-efficient13
   '(let* ([ctc [vectorof (vectorof integer?)]]
           [v (contract
               ctc
               (contract ctc (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! v 0 'bad))
   'neg)

    (test/spec-failed
   'vec-space-efficient14
   '(let* ([ctc (vectorof (vectorof integer? #:immutable #t))]
           [v (contract
               ctc
               (contract ctc (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref v 0))
   "inner-pos")

  (test/spec-passed
   'vectorof-impersonator
   '(let* ([ctc (vectorof (make-contract #:late-neg-projection (lambda (b) (lambda (x n) 'foo))))]
           [v (contract ctc (contract ctc (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;; vector/c contract tests
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (test/spec-failed
   'vector/c-bad-index
   '(let* ([ctc (vector/c (vector/c integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 1 2)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref v 0))
   "inner-pos")

  (test/spec-passed
   'vector/c-space-efficient1
   '(let* ([ctc (vector/c (vector/c integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 0)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 0) 0)))

  (test/spec-failed
   'vector/c-space-efficient2
   '(let* ([ctc (vector/c (vector/c integer?))]
           [v (contract ctc (vector (vector 'bad)) 'inner-pos 'inner-neg)])
      (vector-ref (vector-ref v 0) 0))
   "inner-pos")

  (test/spec-failed
   'vector/c-space-efficient3
   '(let* ([ctc (vector/c (vector/c integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 'bad)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 0) 0))
   "inner-pos")

  (test/spec-failed
   'vector/c-space-efficient4
   '(let* ([ctc (vector/c (vector/c integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! (vector-ref v 0) 0 'bad))
   'neg)

  (test/spec-failed
   'vector/c-space-efficient5
   '(let* ([ctc (vector/c (vector/c integer?))]
           [v (contract
               ctc
               (contract ctc (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! v 0 (vector 'bad))
      (vector-ref (vector-ref v 0) 0))
   'neg)

  ;; non-identical contracts in nested vectorof
  (test/spec-failed
   'vector/c-space-efficient6
   '(let* ([ctc1 (vector/c (vector/c integer?))]
           [ctc2 (vector/c (vector/c positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! (vector-ref v 0) 0 -1))
   "inner-neg")

  (test/spec-failed
   'vector/c-space-efficient7
   '(let* ([ctc1 (vector/c (vector/c integer?))]
           [ctc2 (vector/c (vector/c positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! (vector-ref v 0) 0 1/2))
   'neg)

  (test/spec-failed
      'vector/c-space-efficient8
   '(let* ([ctc1 (vector/c (vector/c integer?))]
           [ctc2 (vector/c (vector/c positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1/2)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 0) 0))
   'pos)

  (test/spec-failed
   'vector/c-space-efficient9
   '(let* ([ctc1 (vector/c (vector/c integer?))]
           [ctc2 (vector/c (vector/c positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector -1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 0) 0))
   "inner-pos")

  ;; tests for various first-order checks performed by vectors
  (test/spec-failed
   'vector/c-space-efficient10
   '(let* ([ctc [vector/c (vector/c integer?)]]
           [v (contract
               ctc
               (contract ctc (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! v 0 'bad))
   'neg)

    (test/spec-failed
     'vector/c-space-efficient11
     '(let* ([ctc (vector/c (vector/c integer? #:immutable #t))]
             [v (contract
                 ctc
                 (contract ctc (vector (vector 1)) 'inner-pos 'inner-neg)
                 'pos 'neg)])
        (vector-ref v 0))
     "inner-pos")

  (test/spec-passed
   'vector/c-impersonator
   '(let* ([ctc (vector/c (make-contract #:late-neg-projection (lambda (b) (lambda (x n) 'foo))))]
           [v (contract ctc (contract ctc (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0)))

  (test/spec-failed
   'vector/c-blame
   '(let* ([ctc (vector/c (-> integer? integer?))]
           [v (contract
               ctc
               (contract ctc (vector add1) 'inner-pos 'inner-neg)
               'pos 'neg)])
      ((vector-ref v 0) 1.5))
   "inner-neg")


  ;; space-efficient continuation marks

  (contract-eval
   '(define (has-space-efficient-mark? v)
      (define marks (current-continuation-marks))
      (define res (continuation-mark-set-first marks space-efficient-contract-continuation-mark-key))
      res))

  (test/spec-passed
   'space-efficient-mark-present
   '(let* ([ctc (vectorof has-space-efficient-mark?)]
           [v (contract ctc (contract ctc (vector 1) 'pos 'neg) 'pos 'neg)])
      (vector-ref v 0)))

  (test/spec-passed/result
   'space-efficient-mark-absent
   '(let* ([ctc (vectorof has-space-efficient-mark?)]
           [v (contract ctc (vector 1) 'pos 'neg)])
      (with-handlers ([exn:fail:contract:blame? (lambda (x) 'passed)])
        (vector-ref v 0)))
   'passed
   1)

  (test/spec-failed
   'vector/c-bailout
   '(let* ([ctc1 (vector/c (vector/c integer?))]
           [ctc2 (vector/c (-> integer?))]
           [v (contract
               ctc2
               (contract
                ctc1
                (vector (vector 1 2))
                'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref v 0))
   "inner-pos")

  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;; Implementation tests
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (contract-eval '(require (submod racket/contract/private/vector-space-efficient for-testing)))
  (contract-eval '(require (submod racket/contract/private/space-efficient-common for-testing)))
  (contract-eval '(define (space-efficient? val) (has-impersonator-prop:multi/c? val)))

  ;; vectorof
  (contract-eval
   '(define (vectorof-has-num-contracts? v ref set)
      (unless (has-impersonator-prop:multi/c? v)
        (error "vectorof-has-num-contracts?: no space-efficient-contract"))
      (define multi/c (get-impersonator-prop:multi/c v))
      (define ref/c (multi-vector-ref-ctcs multi/c))
      (define set/c (multi-vector-set-ctcs multi/c))
      (unless (= (length (multi-leaf/c-proj-list ref/c)) ref)
        (printf "had ~a ref-projs\n\n" (length (multi-leaf/c-proj-list ref/c)))
        (error "vectorof-has-num-contracts?: wrong number of ref projections"))
      (unless (= (length (multi-leaf/c-proj-list set/c)) set)
        (error "vectorof-has-num-contracts?: wrong number of set projections"))
      (unless (= (length (multi-leaf/c-contract-list ref/c)) ref)
        (error "vectorof-has-num-contracts?: wrong number of ref contracts"))
      (unless (= (length (multi-leaf/c-contract-list set/c)) set)
        (error "vectorof-has-num-contracts?: wrong number of set contracts"))))

  (contract-eval
   '(define (vector-can-combine? val ctc)
      (value-has-vector-space-efficient-support? val (chaperone-contract? ctc))))

  ;; vector/c
    (contract-eval
   '(define (vector/c-has-num-contracts? v refs sets)
      (unless (has-impersonator-prop:multi/c? v)
        (error "vectorof-has-num-contracts?: no space-efficient-contract"))
      (define multi/c (get-impersonator-prop:multi/c v))
      (define ref-ctcs (multi-vector-ref-ctcs multi/c))
      (define set-ctcs (multi-vector-set-ctcs multi/c))
      (for ([ref (in-list refs)]
            [ref/c (in-vector ref-ctcs)])
        (unless (= (length (multi-leaf/c-proj-list ref/c)) ref)
          (error "vectorof-has-num-contracts?: wrong number of ref projections"))
        (unless (= (length (multi-leaf/c-contract-list ref/c)) ref)
          (error "vectorof-has-num-contracts?: wrong number of ref contracts")))
      (for ([set (in-list sets)]
            [set/c (in-vector set-ctcs)])
        (unless (= (length (multi-leaf/c-proj-list set/c)) set)
          (error "vectorof-has-num-contracts?: wrong number of set projections"))
        (unless (= (length (multi-leaf/c-contract-list set/c)) set)
          (error "vectorof-has-num-contracts?: wrong number of set contracts")))))

  (contract-eval '(define pos (lambda (x) (and (integer? x) (>= x 0)))))

  (test/spec-passed
   'vecof-num-contracts
   '(let* ([v (contract (vectorof pos) (contract (vectorof pos) (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vectorof-has-num-contracts? v 1 1)))

  (test/spec-passed
   'vecof-num-contracts-different-ref-set
   '(let* ([ctc1 (vectorof (>/c 0))]
           [ctc2 (vectorof real?)]
           [v1 (contract ctc1 (contract ctc1 (vector 1) 'inner-pos 'inner-neg) 'inner-pos 'inner-neg)]
           [v (contract ctc2 (contract ctc2 v1 'pos 'neg) 'pos 'neg)])
      (vectorof-has-num-contracts? v 1 2)))

  (test/spec-passed
   'vec/c-num-contracts
   '(let* ([v (contract (vector/c pos pos) (contract (vector/c pos pos) (vector 1 2) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector/c-has-num-contracts? v '(1 1) '(1 1))))

  (test/spec-passed
   'vec/c-num-contracts-different-ref-set
   '(let* ([ctc1 (vector/c (>/c 0) (>/c 0))]
           [ctc2 (vector/c real? real?)]
           [v1 (contract ctc1 (contract ctc1 (vector 1 2) 'inner-pos 'inner-neg) 'inner-pos 'inner-neg)]
           [v (contract ctc2 (contract ctc2 v1 'pos 'neg) 'pos 'neg)])
      (vector/c-has-num-contracts? v '(1 1) '(2 2))))

  (test/spec-passed
   'vec/c-num-contracts-different-ref-set-different-posns
   '(let* ([ctc1 (vector/c (>/c 0) real?)]
           [ctc2 (vector/c real? real?)]
           [v1 (contract ctc1 (contract ctc1 (vector 1 2) 'inner-pos 'inner-neg) 'inner-pos 'inner-neg)]
           [v (contract ctc2 (contract ctc2 v1 'pos 'neg) 'pos 'neg)])
      (vector/c-has-num-contracts? v '(1 1) '(2 1))))

   (test/spec-passed
   'vec/c-more-ref-than-set
   '(let* ([ctc2 (vector/c (>/c 0) real?)]
           [ctc1 (vector/c real? real?)]
           [v1 (contract ctc1 (contract ctc1 (vector 1 2) 'inner-pos 'inner-neg) 'inner-pos 'inner-neg)]
           [v (contract ctc2 (contract ctc2 v1 'pos 'neg) 'pos 'neg)])
      (vector/c-has-num-contracts? v '(2 1) '(1 1))))

  ;; TODO: a couple more has-num-contracts? tests with one contract sandwiching another for more interesting contract
  ;; merging

  (test/spec-passed
   'vecof-sandwich1
   '(let* ([ctc1 (vectorof integer?)]
           [ctc2 (vectorof real?)]
           [v (contract ctc1 (contract ctc2 (contract ctc1 (vector 1) 'p 'n) 'p 'n) 'p 'n)])
      (vectorof-has-num-contracts? v 2 2)))

  (test/spec-passed
   'vec/c-sandwich1
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c real?)]
           [v (contract ctc1 (contract ctc2 (contract ctc1 (vector 1) 'p 'n) 'p 'n) 'p 'n)])
      (vector/c-has-num-contracts? v '(2) '(2))))


  (test/spec-passed
   'vecof-incompatible1
   '(let* ([ctc1 (vectorof integer?)]
           [ctc2 (vectorof string?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'p 'n) 'p 'n)])
      (vectorof-has-num-contracts? v 2 2)))

  (test/spec-passed
   'vecof-incompatible2
   '(let* ([ctc1 (vectorof integer?)]
           [ctc2 (vectorof string?)]
           [v (contract ctc2 (contract ctc1 (vector 1) 'p 'n) 'p 'n)])
      (vectorof-has-num-contracts? v 2 2)))

  (test/spec-passed
   'vec/c-incompatible1
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c string?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'p 'n) 'p 'n)])
      (vector/c-has-num-contracts? v '(2) '(2))))

  (test/spec-passed
   'vec/c-incompatible2
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c string?)]
           [v (contract ctc2 (contract ctc1 (vector 1) 'p 'n) 'p 'n)])
      (vector/c-has-num-contracts? v '(2) '(2))))

  (test/spec-failed
   'vecof-incompatible1-blame1
   '(let* ([ctc1 (vectorof integer?)]
           [ctc2 (vectorof string?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0))
   "inner-pos")
  (test/spec-failed
   'vecof-incompatible1-blame2
   '(let* ([ctc1 (vectorof integer?)]
           [ctc2 (vectorof string?)]
           [v (contract ctc1 (contract ctc2 (vector "foo") 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0))
   'pos)
  (test/spec-failed
   'vecof-incompatible1-blame3
   '(let* ([ctc1 (vectorof integer?)]
           [ctc2 (vectorof string?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-set! v 0 "foo"))
   'neg)
  (test/spec-failed
   'vecof-incompatible1-blame4
   '(let* ([ctc1 (vectorof integer?)]
           [ctc2 (vectorof string?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-set! v 0 2))
   "inner-neg")

  (test/spec-failed
   'vec/c-incompatible1-blame1
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c string?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0))
   "inner-pos")
  (test/spec-failed
   'vec/c-incompatible1-blame2
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c string?)]
           [v (contract ctc1 (contract ctc2 (vector "foo") 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-ref v 0))
   'pos)
  (test/spec-failed
   'vec/c-incompatible1-blame3
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c string?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-set! v 0 "foo"))
   'neg)
  (test/spec-failed
   'vec/c-incompatible1-blame4
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c string?)]
           [v (contract ctc1 (contract ctc2 (vector 1) 'inner-pos 'inner-neg) 'pos 'neg)])
      (vector-set! v 0 2))
   "inner-neg")

  ;; can combine tests

  (contract-eval
   '(define imp-ctc1
      (make-contract
       #:late-neg-projection (lambda (blame) (lambda (val neg) val)))))

  (contract-eval
   '(define imp-ctc2
      (make-contract
       #:late-neg-projection (lambda (blame) (lambda (val neg) val)))))

  (contract-eval
   '(define chap-ctc
      (make-chaperone-contract
       #:late-neg-projection (lambda (blame) (lambda (val neg) val)))))

  ;; vectorof combine
  (test/spec-passed/result
   'vector-can-combine-chaps
   '(let* ([ctc1 (vectorof integer?)]
           [ctc2 (vectorof real?)]
           [v (contract ctc1 (vector 1) 'pos 'neg)])
      (vector-can-combine? v ctc2))
   #t)

  (test/spec-passed/result
   'vector-can-combine-imps
   '(let* ([ctc1 (vectorof imp-ctc1)]
           [ctc2 (vectorof imp-ctc2)]
           [v (contract ctc1 (vector 1) 'pos 'neg)])
      (vector-can-combine? v ctc2))
   #t)

  (test/spec-passed/result
   'vectorof-cant-mix-chap-imp
   '(let* ([ctc1 (vectorof chap-ctc)]
           [ctc2 (vectorof imp-ctc1)]
           [v (contract ctc1 (vector 1) 'pos 'neg)])
      (vector-can-combine? v ctc2))
   #f)

  (test/spec-passed/result
   'vectorof-cant-mix-imp-chap
   '(let* ([ctc1 (vectorof imp-ctc1)]
           [ctc2 (vectorof chap-ctc)]
           [v (contract ctc1 (vector 1) 'pos 'neg)])
      (vector-can-combine? v ctc2))
   #f)

  (test/spec-passed/result
   'vectorof-cant-merge-if-already-chaperoned
   '(let* ([ctc (vectorof integer?)]
           [v1 (chaperone-vector (vector 1) #f #f)]
           [v (contract ctc v1 'pos 'neg)])
      (vector-can-combine? v ctc))
   #f)

  (test/spec-passed/result
   'vectorof-cant-merge-if-chaperoned-in-se-mode
   '(let* ([ctc (vectorof integer?)]
           [v1 (contract ctc (contract ctc (vector 1) 'pos 'neg) 'pos 'neg)]
           [v (chaperone-vector v1 #f #f)])
      (vector-can-combine? v ctc))
   #f)

  ;; vector/c combine
  (test/spec-passed/result
   'vector-can-combine-chaps
   '(let* ([ctc1 (vector/c integer?)]
           [ctc2 (vector/c real?)]
           [v (contract ctc1 (vector 1) 'pos 'neg)])
      (vector-can-combine? v ctc2))
   #t)

  (test/spec-passed/result
   'vector-can-combine-imps
   '(let* ([ctc1 (vector/c imp-ctc1)]
           [ctc2 (vector/c imp-ctc2)]
           [v (contract ctc1 (vector 1) 'pos 'neg)])
      (vector-can-combine? v ctc2))
   #t)

  (test/spec-passed/result
   'vector/c-cant-mix-chap-imp
   '(let* ([ctc1 (vector/c chap-ctc)]
           [ctc2 (vector/c imp-ctc1)]
           [v (contract ctc1 (vector 1) 'pos 'neg)])
      (vector-can-combine? v ctc2))
   #f)

  (test/spec-passed/result
   'vector/c-cant-mix-imp-chap
   '(let* ([ctc1 (vector/c imp-ctc1)]
           [ctc2 (vector/c chap-ctc)]
           [v (contract ctc1 (vector 1) 'pos 'neg)])
      (vector-can-combine? v ctc2))
   #f)

  (test/spec-passed/result
   'vector/c-cant-merge-if-already-chaperoned
   '(let* ([ctc (vector/c integer?)]
           [v1 (chaperone-vector (vector 1) #f #f)]
           [v (contract ctc v1 'pos 'neg)])
      (vector-can-combine? v ctc))
   #f)

  (test/spec-passed/result
   'vector/c-cant-merge-if-chaperoned-in-se-mode
   '(let* ([ctc (vector/c integer?)]
           [v1 (contract ctc (contract ctc (vector 1) 'pos 'neg) 'pos 'neg)]
           [v (chaperone-vector v1 #f #f)])
      (vector-can-combine? v ctc))
   #f)


  (contract-eval
   '(define many-layers
      (contract (vectorof even?)
                (chaperone-vector
                 (contract (vectorof exact-integer?)
                           (contract (vectorof positive?)
                                     (vector 2)
                                     'pos1 'neg1)
                           'pos2 'neg2)
                 #f
                 #f)
                'pos3 'neg3)))

  (test/spec-failed
   'many-layers-neg1
   '(vector-set! many-layers 0 0)
   "neg1")
  (test/spec-failed
   'many-layers-neg2
   '(vector-set! many-layers 0 2.0)
   "neg2")
  (test/spec-failed
   'many-layers-neg3
   '(vector-set! many-layers 0 1)
   "neg3")

  (contract-eval
   '(define many-layers/c
      (contract (vector/c even?)
                (chaperone-vector
                 (contract (vector/c exact-integer?)
                           (contract (vector/c positive?)
                                     (vector 2)
                                     'pos1 'neg1)
                           'pos2 'neg2)
                 #f
                 #f)
                'pos3 'neg3)))

  (test/spec-failed
   'many-layers/c-neg1
   '(vector-set! many-layers/c 0 0)
   "neg1")
  (test/spec-failed
   'many-layers/c-neg2
   '(vector-set! many-layers/c 0 2.0)
   "neg2")
  (test/spec-failed
   'many-layers/c-neg3
   '(vector-set! many-layers/c 0 1)
   "neg3")

  ;; Vector Sorting Tests
  ;; Make sure that if we sort a vector of vectors
  ;; that must ref each element at least n times that the
  ;; contained vectors do not build up contracts
  
  (contract-eval
   '(define (my-sort vec)
      (define length (vector-length vec))
      (for ([i (in-range length)])
        (for ([j (in-range i length)])
          (define vi (vector-ref vec i))
          (define vj (vector-ref vec j))
          (when (< (vector-ref vj 0) (vector-ref vi 0))
            (vector-set! vec i vj)
            (vector-set! vec j vi))))))

  (contract-eval
   '(define unsorted (vector
                      (vector 10)
                      (vector 9)
                      (vector 8)
                      (vector 7)
                      (vector 6)
                      (vector 5)
                      (vector 4)
                      (vector 3)
                      (vector 2)
                      (vector 1))))

  (contract-eval
   '(define unsorted+contracted
      (contract (vectorof (vectorof integer?))
                unsorted
                'pos 'neg)))

  (test/spec-passed
   'vecof-sorting
   '(let ()
      (my-sort unsorted+contracted)
      (for ([v (in-vector unsorted+contracted)])
        (vectorof-has-num-contracts? v 1 1))))

  (contract-eval
   '(define unsorted2 (vector
                      (vector 10)
                      (vector 9)
                      (vector 8)
                      (vector 7)
                      (vector 6)
                      (vector 5)
                      (vector 4)
                      (vector 3)
                      (vector 2)
                      (vector 1))))

  (contract-eval
   '(define unsorted+contracted-vector/c
      (contract (vector/c (vector/c integer?)
                          (vector/c integer?)
                          (vector/c integer?)
                          (vector/c integer?)
                          (vector/c integer?)
                          (vector/c integer?)
                          (vector/c integer?)
                          (vector/c integer?)
                          (vector/c integer?)
                          (vector/c integer?))
                unsorted2
                'pos 'neg)))

  (test/spec-passed
   'vecof-sorting
   '(let ()
      (my-sort unsorted+contracted-vector/c)
      (for ([v (in-vector unsorted+contracted-vector/c)])
        (vector/c-has-num-contracts? v '(1) '(1)))))

  ;; bail out and switching bugs

  (contract-eval '(require racket/class))

  (test/spec-passed
   'object/c-passing-vecof
   '(let* ([grid/c (vectorof (vectorof (object/c)))]
           [grid (contract
                  grid/c
                  (contract
                   grid/c
                   (vector (vector (new object%)))
                   'inner-pos 'inner-neg)
                  'pos 'neg)])
      (vector-ref (vector-ref grid 0) 0)))

  (test/spec-failed
   'object/c-failing-vecof
   '(let* ([v (contract (vectorof integer?) (vector 1) 'orig-p 'orig-n)]
           [grid/c (vectorof (vectorof (object/c)))]
           [grid (contract
                  grid/c
                  (contract
                   grid/c
                   (vector v)
                   'inner-pos 'inner-neg)
                  'pos 'neg)])
      (vector-ref (vector-ref grid 0) 0))
   "inner-pos")

  (test/spec-passed
   'object/c-passing-vec/c
   '(let* ([grid/c (vector/c (vector/c (object/c)))]
           [grid (contract
                  grid/c
                  (contract
                   grid/c
                   (vector (vector (new object%)))
                   'inner-pos 'inner-neg)
                  'pos 'neg)])
      (vector-ref (vector-ref grid 0) 0)))

  (test/spec-failed
   'object/c-failing-vecof
   '(let* ([v (contract (vector/c integer?) (vector 1) 'orig-p 'orig-n)]
           [grid/c (vector/c (vector/c (object/c)))]
           [grid (contract
                  grid/c
                  (contract
                   grid/c
                   (vector v)
                   'inner-pos 'inner-neg)
                  'pos 'neg)])
      (vector-ref (vector-ref grid 0) 0))
   "inner-pos")

  (contract-eval '(define (double-wrapped? x)
                    (has-impersonator-prop:multi/c?
                     (get-impersonator-prop:checking-wrapper x))))

  (test-false
   'dont-multi-wrap
   '(let* ([ctc (vectorof (vectorof integer?))]
           [v (contract ctc (contract ctc (vector (vector 1)) 'ip 'in) 'p 'n)]
           [v2 (contract (vectorof any/c) v 'p2 'n2)])
      (double-wrapped? v2)))
  )
