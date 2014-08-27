#lang racket/base

;; This module provides helper functions for typed signatures

(require "../utils/utils.rkt"
         (env signature-env)
         (rep type-rep)
        ; (private parse-type)
         syntax/parse
         racket/list
         (only-in racket/set subset?)
         (for-template racket/base
                       (typecheck internal-forms)))

(provide parse-signature
         check-sub-signatures?)

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
     (list (syntax->datum #'name) #'type)]))

;; check-subsignatures? : (listof Signature) (listof Signature) -> boolean?
;; checks that the first list of signatures is a valid "subtype"/extensions
;; of the second list of signatures
(define (check-sub-signatures? sub-sigs sup-sigs)
  (define sub-exts (append-map signature-extensions sub-sigs))
  (define sup-exts (append-map signature-extensions sup-sigs))
  (subset? sup-exts sub-exts))

;; signature-extensions : (or/c #f Signature) -> (listof identifier?)
;; returns the list (chain) of names of each signature that
;; the given signature extends including itself
;; returns '() when given #f
(define (signature-extensions sig)
  (if sig
      (cons (Signature-name sig)
            (signature-extensions (Signature-extends sig)))
      null))
