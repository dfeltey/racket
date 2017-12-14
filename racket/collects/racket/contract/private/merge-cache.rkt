#lang racket/base

(provide define/merge-cache)

(require (for-syntax racket/base))

;; How to evict things from the cache after some length of time ...
;; Which functions are safe to put in the cache?
;; known-good-contract?
;; log all the predicates used in the benchmark
;; TODO: use a thread cell here ...

;; weak hashtable never cleared
;; if reach a threshold, throw away and start over
;; limit cache size to 10, and use some LRU policy (sort ...) (priority queue)
;; make define/merged-cache form to define caches in  the 3 places .. 
(struct limit-cache (size table) #:mutable)
(define LIMIT 10)
(define (increment/clear-cache lc size)
  (cond
    [((add1 size) . > . LIMIT)
     (set-limit-cache-size! lc 0)
     (set-limit-cache-table! lc (make-weak-hasheq))]
    [else
     (set-limit-cache-size! lc (add1 size))]))

(define MERGE-CACHE (make-thread-cell (limit-cache 0 (make-weak-hasheq))))

(require (for-syntax racket/base))
(define-syntax (define/merge-cache stx)
  (syntax-case stx ()
    [(_ (merge-name new-se new-neg old-se old-neg) body ...)
     #'(define (merge-name new-se new-neg old-se old-neg)
         (call-with-merge-cache new-se new-neg old-se old-neg
           (λ () body ...)))]))

(define (call-with-merge-cache new-se new-neg old-se old-neg body-thunk)
  (define the-cache (thread-cell-ref MERGE-CACHE))
  (define size (limit-cache-size the-cache))
  (define table (limit-cache-table the-cache))
  (define h1 (hash-ref table new-se #f))
  (cond
    [h1
     (define h2 (hash-ref h1 new-neg #f))
     (cond
       [h2
        (define h3 (hash-ref h2 old-se #f))
        (cond
          [h3
           (define cached-result (hash-ref h3 old-neg #f))
           (cond
             [(ephemeron-value cached-result) => values]
             [else
              (define result (body-thunk))
              (hash-set! h3 old-neg (make-ephemeron old-neg result))
              (increment/clear-cache the-cache size)
              result])]
          [else
           (define result (body-thunk))
           (define h3 (make-hasheq (list (cons old-neg (make-ephemeron old-neg result)))))
           (hash-set! h2 old-se h3)
           (increment/clear-cache the-cache size)
           result])]
       [else
        (define result (body-thunk))
        (define h3 (make-hasheq (list (cons old-neg (make-ephemeron old-neg result)))))
        (define h2 (make-hasheq (list (cons old-se h3))))
        (hash-set! h1 new-neg h2)
        (increment/clear-cache the-cache size)
        result])]
    [else
     (define result (body-thunk))
     (define h3 (make-hasheq (list (cons old-neg (make-ephemeron old-neg result)))))
     (define h2 (make-hasheq (list (cons old-se h3))))
     (define h1 (make-hasheq (list (cons new-neg h2))))
     (hash-set! table new-se h1)
     (increment/clear-cache the-cache size)
     result]))
