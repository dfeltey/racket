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

  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;
  ;; Implementation tests
  ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (contract-eval '(require (submod racket/contract/private/vector-space-efficient for-testing)))
  (contract-eval '(define (space-efficient? val) (has-impersonator-prop:multi/c? val)))
  
  ;; vectorof
  (contract-eval
   '(define (vectorof-has-num-contracts? v ref set)
      (unless (has-impersonator-prop:multi/c? c)
        (error "vectorof-has-num-contracts?: no space-efficient-contract"))
      (define multi/c (get-impersonator-prop:multi/c v))
      (define ref/c (multi-vectorof-ref-ctc multi/c))
      (define set/c (multi-vectorof-set-ctc multi/c))
      (unless (= (length (multi-leaf/c-proj-list ref/c)) ref)
        (error "vectorof-has-num-contracts?: wrong number of ref projections"))
      (unless (= (length (multi-leaf/c-proj-list set/c)) set)
        (error "vectorof-has-num-contracts?: wrong number of set projections"))
      (unless (= (length (multi-leaf/c-contract-list ref/c)) ref)
        (error "vectorof-has-num-contracts?: wrong number of ref contracts"))
      (unless (= (length (multi-leaf/c-contract-list set/c)) set)
        (error "vectorof-has-num-contracts?: wrong number of set contracts"))))

  (contract-eval
   '(define (vectorof-can-combine? val ctc)
      (value-has-vectorof-space-efficient-support? val (chaperone-contract? ctc))))


  (contract-eval '(define pos (lambda (x) (and (integer? x) (>= x 0)))))
  (contract-eval '(define vecof-pos (vectorof pos)))
  (contract-eval '(define vecof-vecof-pos (vectorof vecof-pos)))
  
      
  
  ;; vector/c
    (contract-eval
   '(define (vector/c-has-num-contracts? v refs sets)
      (unless (has-impersonator-prop:multi/c? c)
        (error "vectorof-has-num-contracts?: no space-efficient-contract"))
      (define multi/c (get-impersonator-prop:multi/c v))
      (define ref-ctcs (multi-vector/c-ref-ctcs multi/c))
      (define set-ctcs (multi-vector/c-set-ctcs multi/c))
      (for ([ref (in-list refs)]
            [ref/c (in-list ref-ctcs)])
        (unless (= (length (multi-leaf/c-proj-list ref/c)) ref)
          (error "vectorof-has-num-contracts?: wrong number of ref projections"))
        (unless (= (length (multi-leaf/c-contract-list ref/c)) ref)
          (error "vectorof-has-num-contracts?: wrong number of ref contracts")))
      (for ([set (in-list sets)]
            [set/c (in-list set-ctcs)])
        (unless (= (length (multi-leaf/c-proj-list set/c)) set)
          (error "vectorof-has-num-contracts?: wrong number of set projections"))
        (unless (= (length (multi-leaf/c-contract-list set/c)) set)
          (error "vectorof-has-num-contracts?: wrong number of set contracts")))))

    (contract-eval
     '(define (vector/c-can-combine? val ctc)
        (value-has-vector/c-space-efficient-support? val (chaperone-contract? ctc))))


  ;; TODO: sorting test
  

  )
