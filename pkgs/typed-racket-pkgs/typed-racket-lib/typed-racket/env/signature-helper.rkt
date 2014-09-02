#lang racket/base

;; This module provides helper functions for typed signatures

(require "../utils/utils.rkt"
         (env signature-env)
         (rep type-rep)
         (private parse-type)
         syntax/parse
         racket/list
         (only-in racket/set subset?)
         (for-template racket/base
                       (typecheck internal-forms)))

(provide parse-signature)

;; parse-signature : Syntax -> identifier? Signature
;; parses the internal signature form to build a signature
(define (parse-signature form)
  (syntax-parse form
    #:literal-sets (kernel-literals)
    #:literals (values define-signature-internal)
    [(define-values ()
       (begin (quote-syntax (define-signature-internal name super (binding ...)))
              (#%plain-app values)))
      (define extends (and (syntax->datum #'super) (lookup-signature #'super)))
      (define mapping (map parse-signature-binding (syntax->list #'(binding ...))))
      (values #'name (make-Signature #'name extends mapping))]))

;; parse-signature-binding : Syntax -> (list/c symbol? Type/c)
;; parses the binding forms inside of a define signature into the 
;; form used by the Signature type representation
(define (parse-signature-binding binding-stx)
  (syntax-parse binding-stx
    [[name:id type]
     (list (syntax->datum #'name) (parse-type #'type))]))

