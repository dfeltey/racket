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

(provide parse-signature signature->bindings signatures->bindings)

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

;; parse-signature-binding : Syntax -> (list/c identifier? syntax?)
;; parses the binding forms inside of a define signature into the 
;; form used by the Signature type representation
(define (parse-signature-binding binding-stx)
  (syntax-parse binding-stx
    [[name:id type]
     (cons #'name #'type)]))

;; signature->bindings : identifier? -> (listof (cons/c identifier? syntax?))
;; GIVEN: a signature name
;; RETURNS: the list of variables bound by that signature
;;          inherited bindings come first
(define (signature->bindings sig-id)
  (define sig (lookup-signature sig-id))
  (let loop ([sig (Signature-extends sig)]
             [mapping (Signature-mapping sig)]
             [bindings null])
    (if sig
        (loop (Signature-extends sig) (Signature-mapping sig) (append mapping bindings))
        (append mapping bindings))))

;; (listof identifier?) -> (listof (cons/c identifier? syntax?))
;; GIVEN: a list of signature names
;; RETURNS: the list of all bindings from those signatures
;; TODO: handle required renamings/prefix/only/except
(define (signatures->bindings ids)
  (apply append (map signature->bindings ids)))



