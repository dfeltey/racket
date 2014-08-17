#lang racket/base

;; This module provides helper functions for typed signatures

(require "../utils/utils.rkt"
         (utils tc-utils)
         (env type-alias-env type-name-env signature-env)
         (rep type-rep)
         (private parse-type)
         (typecheck internal-forms)
         syntax/kerncase)

(provide parse-signature)

;; parse-signature : Syntax -> identifier? Signature
;; parses the internal signature form to build a signature
(define (parse-signature form)
  (kernel-syntax-case* form #f
    (define-signature-internal values)
    [(define-values ()
       (begin (quote-syntax (define-signature-internal name super (binding ...)))
              (#%plain-app values)))
     (let () 
       (define extends (lookup-signature #'super))
       (define mapping (syntax->list #'(binding ...)))
       (values #'name (make-Signature #'name extends mapping)))]))
