#lang racket/base

;; Primitive forms for units/signatures

(provide define-signature unit)

(require  "../utils/utils.rkt"
          (for-syntax syntax/parse
                      racket/base
                      racket/list
                      syntax/context
                      syntax/flatten-begin
                      syntax/kerncase
                      "../private/syntax-properties.rkt"
                     ; (private parse-type)
                     ; (rep type-rep)
                     ; (env signature-helper)
                      syntax/id-table
                      racket/dict
                      )
          (only-in racket/unit 
                   [define-signature untyped-define-signature] 
                   [unit untyped-unit]
                   extends
                   import
                   export
                   init-depend)
          "../typecheck/internal-forms.rkt"
          (for-label "colon.rkt")
          (for-template (rep type-rep)))

(begin-for-syntax
  ;; a binding is a (binding identifier? syntax?)
  ;; id is the name of the variable being bound
  ;; type is the syntax of the type associated with the variable
  (struct binding (id type))

  ;; a sig is a (sig identifier? (or/c identifer? #f) (listof (list/c identifier? syntax?))
  ;; name is the identifier representing the signature
  ;; extends is either the id of an extended signature or #f if the signature is not an extension
  ;; mapping is the list of bindings introduced in this signatures definition
  (struct sig (name extends mapping) #:transparent)
  
  ;; need an environment that updates when define-signature expands, and can
  ;; be queried when the unit macro expands
  (define pre-sig-env (make-free-id-table))

  (define (register-pre-sig-env! id sig)
    (free-id-table-set! pre-sig-env id sig))

  (define (lookup-sig id)
    (if (identifier? id)
        (free-id-table-ref pre-sig-env id #f)
        #f))

  (define (sig->bindings sig-id)
    (define sig (lookup-sig sig-id))
    (let loop ([sig (sig-extends sig)]
               [mapping (sig-mapping sig)]
               [bindings null])
      (if sig
          (loop (sig-extends sig) (sig-mapping sig) (append bindings mapping))
          (append bindings mapping))))


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
             #:with extends-id #'super
             #:attr form #'(extends super))
    (pattern (~seq)
             #:with internal-form #'#f
             #:with extends-id '()
             #:attr form '()))

  (define-splicing-syntax-class init-depend-form
    #:literals (init-depend)
    (pattern (init-depend sig:id ...)
             #:attr form '(#'(init-depend sig ...)))
    (pattern (~seq)
             #:attr form '()))
  
  (define-syntax-class unit-expr
    (pattern e
             #:with val #'e))

  ;; parse-binding : syntax -> binding?
  ;; parses a  def-sig form and returns the binding representation
  (define (parse-binding stx)
    (syntax-parse stx
      [form:def-sig-form
       (apply binding (syntax->list #'form.internal-form))]))

  ;; local expansion for unit body expressions
  ;; based on expand-expressions in class-prims
  (define (expand-unit-expressions stxs ctx def-ctx)
    (define (unit-expand stx)
      (local-expand stx ctx (kernel-form-identifier-list) def-ctx))
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
                 (syntax->list #'(name ...)) #f def-ctx) 
                (cons stx (loop (cdr stxs)))]
                [_ (cons stx (loop (cdr stxs)))])])))
  
  #;
  (define (annotate-unit-body-expr e)
    (syntax-parse e
      #:literals (define-values define-syntaxes)
      [(define-values (id ...) . rst)
       
       ]))
  
  ;; same trick as for classes to recover names
  (define (make-locals-table import-names export-names)
    (tr:unit:local-table-property
     #`(let-values ([(#,@import-names)
                     (values #,@(map (lambda (stx) #`(lambda () #,stx (set! #,stx 0)))
                                     import-names))]
                    [(#,@export-names)
                     (values #,@(map (lambda (stx) #`(lambda () #,stx (set! #,stx 0)))
                                     export-names))])
         (void))
     #t)))


(define-syntax (define-signature stx)
  (syntax-parse stx
    [(_ sig-name:id super-form:extends-form (form:def-sig-form ...))
     (define name #'sig-name)
     (define extends (lookup-sig #'super-form.extends-id))
     (define mapping (map parse-binding (syntax->list #'(form ...))))
     (define sig-elt (sig name extends mapping))
     (register-pre-sig-env! name sig-elt)
     (ignore
      (quasisyntax/loc stx
        (begin
          #,(internal #'(define-signature-internal sig-name super-form.internal-form (form.internal-form ...)))
          (untyped-define-signature sig-name #,@(attribute super-form.form) (form.erased ...)))))]))

(define-syntax (unit stx)
  (syntax-parse stx
    #:literals (import export)
    [(unit (import import-sig:id ...)
           (export export-sig:id ...)
           init-depends:init-depend-form
           e:unit-expr ...)
     (define unit-ctx (generate-expand-context))
     (define def-ctx (syntax-local-make-definition-context))
     (define expanded-stx (expand-unit-expressions (syntax->list #'(e ...)) unit-ctx def-ctx))
     (define imported-sig-ids (syntax->list #'(import-sig ...)))
     (define exported-sig-ids (syntax->list #'(export-sig ...)))
     (define import-names (map binding-id (apply append (map sig->bindings imported-sig-ids))))
     (define export-names (map binding-id (apply append (map sig->bindings exported-sig-ids))))
     (syntax-parse expanded-stx
       [(e:unit-expr ...)
        (internal-definition-context-seal def-ctx)
        ;(define annotated-exprs (map annotate-unit-body-expr (syntax->list #'(e ...))))
        (let ()
          (printf "expanding ...")
          (ignore
           (tr:unit
            (quasisyntax/loc stx
              (let-values ()
                ;; ??
                (untyped-unit (import import-sig ...)
                              (export export-sig ...)
                              #,@(attribute init-depends.form)
                              #,(make-locals-table import-names export-names)
                              e.val ...))))))])]))
