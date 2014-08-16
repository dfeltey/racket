#lang racket/base

;; Environment for signature definitions
;; to track bindings and type definitions inside of signatures

(provide register-signature!
         lookup-signature)

(require syntax/id-table)

;; initial signature environment
(define signature-env (make-free-id-table))

;; register-signature! : identifier? Signature? -> Void
;; adds a mapping from the given identifier to the given signature
;; in the signature environment
(define (register-signature! id sig) 
  (free-id-table-set! signature-env id sig))

;; lookup-signature : identifier? -> (or/c #f Signature?)
;; look up the signature corresponding to the given identifier
;; in the signature environment
(define (lookup-signature id) 
  (free-id-table-ref signature-env id #f))
