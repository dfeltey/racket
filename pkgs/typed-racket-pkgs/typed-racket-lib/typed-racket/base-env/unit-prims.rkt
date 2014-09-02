#lang racket/base

;; Primitive forms for units/signatures

(provide define-signature)

(require (for-syntax syntax/parse
                     racket/base
                     syntax/context
                     syntax/flatten-begin
                     syntax/kerncase
                     "../private/syntax-properties.rkt")
         (only-in racket/unit 
                  [define-signature untyped-defined-signature] 
                  [unit untyped-unit]
                  extends
                  import
                  export
                  init-depend)
         "../typecheck/internal-forms.rkt"
         (for-label "colon.rkt"))

(begin-for-syntax 
  (define-literal-set colon #:for-label (:))
  
  ;; TODO: extend for other sig forms
  (define-syntax-class def-sig-form
    #:literal-sets (colon)
    (pattern [name:id : type]
             #:with internal-form #'(name type)
             #:with erased #'name))

  (define-splicing-syntax-class extends-form
    #:literals (extends)
    (pattern (~seq extends super:id)
             #:with internal-form #'super
             #:attr form '(#'extends #'super))
    (pattern (~seq)
             #:with internal-form #'#f
             #:attr form '()))

  (define-splicing-syntax-class init-depend-form
    #:literals (init-depend)
    (pattern (init-depend sig:id ...)
             #:attr form '(#'(init-depend sig ...)))
    (pattern (~seq)
             #:attr form '()))
  
  (define-syntax-class unit-clause)

  ;; local expansion for unit body expressions
  ;; based on expand-expressions in class-prims
  (define (expand-unit-expressions stxs ctx def-ctx)
    (define (unit-expand stx)
      (local-expand stx ctx kernel-form-identifier-list def-ctx))
    (let loop ([stxs stxs])
      (cond [(null? stxs) null]
            [else
             (define stx (unit-expand (car stxs)))
             (syntax-parse stx 
               #:literals (begin define-syntaxes define-values)
               [(begin . _)
                (loop (append (flatten-begin stx) (cdr stxs)))]
               [(define-syntaxes (name:id ...) rhs:expr)
                (syntax-local-bind-syntaxes
                 (syntax->list #'(name ...)) #'rhs def-ctx)
                (cons stx (loop (cdr stxs)))]
               [(define-values (name:id ...) rhs:expr)
                (syntax-local-bind-syntaxes
                 (syntax->list #'(name ...) #f def-ctx)
                 (cons stx (loop (cdr stxs))))]
                [_ (cons stx (loop (cdr stxs)))])]))))


(define-syntax (define-signature stx)
  (syntax-parse stx
    [(_ name:id super-form:extends-form (form:def-sig-form ...))
     (quasisyntax/loc stx
       (begin
         #,(internal #`(untyped-define-signature name #,@(attribute super-form.form)
                                                 (form.erased ...)))
         #,(internal #'(define-signature-internal name super-form.internal-form (form.internal-form ...)))))]))

(define-syntax (unit stx)
  (syntax-parse stx
    #:literals (import export)
    [(unit (import import-sig:id ...)
           (export export-sig:id ...)
           init-depends:init-depend-form
           e:expr ...)
     (define unit-ctx (generate-expand-context))
     (define def-ctx (syntax-local-make-definition-context))
     (define expanded-stx (expand-unit-expressions (syntax->list #'(e ...)) unit-ctx def-ctx))
     (define imported-sig-ids (syntax->list #'(import-sig ...)))
     (define exported-sig-ids (syntax->list #'(export-sig ...)))
     (syntax-parse expanded-stx
       [_
        (ignore
         (tr:unit
          (quasisyntax/loc stx
            (let-values ()
              ;; ??
              (untyped-unit (import import-sig ...)
                            (export export-sig ...)
                            #,@(attribute init-depends.form)
                            e ...)))))])]))
