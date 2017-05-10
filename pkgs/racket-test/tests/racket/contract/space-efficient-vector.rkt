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

  
  )

  
