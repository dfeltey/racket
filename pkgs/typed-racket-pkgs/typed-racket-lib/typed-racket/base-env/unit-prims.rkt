#lang racket/base

;; Primitive forms for units/signatures

(provide define-signature unit unit-tags)


(require  "../utils/utils.rkt"
          "colon.rkt"
          (for-syntax syntax/parse
                      racket/base
                      racket/list
                      racket/syntax
                      syntax/context
                      syntax/flatten-begin
                      syntax/kerncase
                      "../private/syntax-properties.rkt"
                     ; (private parse-type)
                     ; (rep type-rep)
                     ; (env signature-helper)
                      syntax/id-table
                      racket/dict
                      racket/unit-exptime
                      syntax/strip-context)
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
  
  (define (remove-identifiers-from-definition-context ids def-ctx)
    (map (lambda (id) (identifier-remove-from-definition-context id def-ctx)) ids))

  ;; local expansion for unit body expressions
  ;; based on expand-expressions in class-prims
  (define (expand-unit-expressions stxs ctx def-ctx)
    (define (unit-expand stx)
      (local-expand stx ctx (append  (kernel-form-identifier-list) (list 
                                                                    ;(quote-syntax :)
                                                                    )) def-ctx))
    (let loop ([stxs stxs]
               [names '()])
      (cond [(null? stxs) (values null names)]
            [else
             (define stx (unit-expand (car stxs)))
             (syntax-parse stx
               #:literals (begin define-syntaxes define-values)
               [(begin . _)
                (loop (append (flatten-begin stx) (cdr stxs)) names)]
               [(define-syntaxes (name:id ...) rhs:expr)
                (syntax-local-bind-syntaxes
                 (syntax->list #'(name ...)) #'rhs def-ctx)
                (define-values (estxs enames) (loop (cdr stxs) names))
                ;;(cons stx (loop (cdr stxs)))
                (values (cons stx estxs) enames)]
               [(define-values (name:id ...) rhs:expr)
                (syntax-local-bind-syntaxes
                 (syntax->list #'(name ...)) #f def-ctx)
                (define-values (estxs enames) (loop (cdr stxs) (append (syntax->list #'(name ...)) names)))
                ;;(cons stx (loop (cdr stxs)))
                (values (cons stx estxs) enames)]
               [_ 
                (define-values (estxs enames) (loop (cdr stxs) names))
                ;;(cons stx (loop (cdr stxs) names))
                (values (cons stx estxs) enames)])])))
  
  
  
  #;
  (define (annotate-unit-body-expr e)
    (syntax-parse e
      #:literals (define-values define-syntaxes)
      [(define-values (id ...) . rst)
       
       ]))
  
  ;; extract vars from a signature with the correct syntax marks
  ;; I have no idea why this works, or is necessary
  ;; TODO: this is probably not general enough and will need to be modified
  ;; to deal with prefix/rename when those are implemented for TR units
  (define (get-signature-vars sig-id)
    (define-values (_0 vars _2 _3)
      ;; TODO: give better argument for error-stx
      (signature-members sig-id sig-id))
    (map 
     (lambda (id)
       (syntax-local-introduce
        (syntax-local-get-shadower
         ((lambda (id-inner) 
            (syntax-local-introduce 
             ((syntax-local-make-delta-introducer sig-id) id-inner))) id))))
     vars))
  
  (define (get-signatures-vars stx)
    (define sig-ids (syntax->list stx))
    (apply append (map (lambda (sig-id) (get-signature-vars sig-id)) sig-ids)))

  ;; same trick as for classes to recover names
  (define (make-locals-table names)
    (tr:unit:local-table-property
     #`(let-values ([(#,@names)
                     (values #,@(map (lambda (stx) #`(lambda () (#,stx)))
                                     names))])
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




(define-syntax (add-tags stx)
  (syntax-parse stx
    [(add-tags e)
     (define e-stx (local-expand #'e
                                 (syntax-local-context)
                                 (kernel-form-identifier-list)))
     (syntax-parse e-stx
        #:literals (begin define-syntaxes define-values :)
        [(begin b ...) #'(add-tags b ...)]
        [(define-syntaxes (name:id ...) rhs:expr)
         e-stx]
        [(define-values (name:id ...) rhs:expr)
         (define names (syntax->list #'(name ...)))
         (define def-stx
           #`(define-values (name ...)
               #,(tr:unit:body-expr-or-annotation-property #'rhs 'ann/defn)))
         (if (null? names)
             def-stx
             #`(begin
                 #,def-stx
                 #,(make-locals-table names)))]
        [_
         (tr:unit:body-expr-or-annotation-property e-stx 'expr)])]
    [(add-tags e ...)
     #'(begin
         (add-tags e) ...)]))

(define-syntax (unit-tags stx)
  (syntax-parse stx
    #:literals (import export)
    [(unit (import import-sig:id ...)
           (export export-sig:id ...)
           init-depends:init-depend-form
           e:unit-expr ...)
     (let ()
       (printf "expanding unit-tags ...\n")
       (ignore
        (tr:unit
         (quasisyntax/loc stx
             (let-values ()
               (untyped-unit (import import-sig ...)
                             (export export-sig ...)
                             #,@(attribute init-depends.form)
                             #,(make-locals-table (get-signatures-vars #'(import-sig ...)))
                             (add-tags e ...)))))))]))


(define-syntax (unit stx)
  (syntax-parse stx
    #:literals (import export)
    [(unit (import import-sig:id ...)
           (export export-sig:id ...)
           init-depends:init-depend-form
           e:unit-expr ...)
     (define unit-ctx (generate-expand-context))
     (define def-ctx (syntax-local-make-definition-context))
     (define-values (expanded-stx def-names) (expand-unit-expressions (syntax->list #'(e ...)) unit-ctx def-ctx))
     (internal-definition-context-seal def-ctx)
     (syntax-parse expanded-stx
       [(e-exp:unit-expr ...)
        ;;(define annotated-exprs (map annotate-unit-body-expr (syntax->list #'(e ...))))
        (let ()
          (printf "expanding ...")
          (ignore
           (tr:unit
            (with-syntax ([(new-import-sig ...) 
                           (map (lambda (sig-id) (internal-definition-context-apply def-ctx sig-id))
                                (syntax->list #'(import-sig ...)))]
                          [(new-export-sig ...) 
                           (map (lambda (sig-id) (internal-definition-context-apply def-ctx sig-id))
                                (syntax->list #'(export-sig ...)))]) 
              (quasisyntax/loc stx
                (let-values ()
                  ;; ??
                  (untyped-unit (import new-import-sig ...)
                                (export new-export-sig ...)
                                #,@(attribute init-depends.form)
                                
                                #;
                                #,(make-locals-table (get-signatures-vars #'(import-sig ...) stx) 
                                                     (get-signatures-vars #'(export-sig ...) stx)
                                                     def-names)
                                e-exp ...)))))))])]))
