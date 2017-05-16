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
   'vec-space-efficient8
   '(let* ([ctc1 (vectorof (vectorof integer?))]
           [ctc2 (vectorof (vectorof positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! (vector-ref v 0) 0 -1))
   "inner-neg")

  (test/spec-failed
   'vec-space-efficient8
   '(let* ([ctc1 (vectorof (vectorof integer?))]
           [ctc2 (vectorof (vectorof positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! (vector-ref v 0) 0 1/2))
   'neg)

  (test/spec-failed
   'vec-space-efficient8
   '(let* ([ctc1 (vectorof (vectorof integer?))]
           [ctc2 (vectorof (vectorof positive?))]
           [v (contract
               ctc1
               (contract ctc2 (vector (vector 1/2)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-ref (vector-ref v 0) 0))
   'pos)

  (test/spec-failed
   'vec-space-efficient8
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
   'vec-space-efficient8
   '(let* ([ctc [vectorof (vectorof integer?)]]
           [v (contract
               ctc
               (contract ctc (vector (vectorof 1)) 'inner-pos 'inner-neg)
               'pos 'neg)])
      (vector-set! v 0 'bad))
   'neg)


  
  )

  
