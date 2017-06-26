#lang racket/base

(require "blame.rkt")

(provide (struct-out base-vectorof)
         (struct-out base-vector/c)
         do-check-vectorof
         check-vector/c)

;; eager is one of:
;; - #t: always perform an eager check of the elements of an immutable vector
;; - #f: never  perform an eager check of the elements of an immutable vector
;; - N (for N>=0): perform an eager check of immutable vectors size <= N
(define-struct base-vectorof (elem immutable eager))

(define-struct base-vector/c (elems immutable))


(define (do-check-vectorof val fail immutable)
  (unless (vector? val)
    (fail val '(expected "a vector," given: "~e") val))
  (cond
    [(eq? immutable #t)
     (unless (immutable? val)
       (fail val '(expected "an immutable vector" given: "~e") val))]
    [(eq? immutable #f)
     (when (immutable? val)
       (fail val '(expected "an mutable vector" given: "~e") val))]
    [else (void)]))

(define (check-vector/c val blame immutable length)
  (define (raise-blame val . args)
    (apply raise-blame-error blame #:missing-party #f val args))
  (do-check-vectorof val raise-blame immutable)
  (unless (or (not length) (= (vector-length val) length))
    (raise-blame val
                 '(expected: "a vector of ~a element~a" given: "~e")
                 length
                 (if (= length 1) "" "s")
                 val)))
