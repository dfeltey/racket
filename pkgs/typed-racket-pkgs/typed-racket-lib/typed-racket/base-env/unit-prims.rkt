#lang racket/base

;; Primitive forms for units/signatures

(provide define-signature unit)


(require  "../utils/utils.rkt"
          "colon.rkt"
          "../private/unit-literals.rkt"
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
             #:attr form (list #'(init-depend sig ...))
             #:with names #'(sig ...))
    (pattern (~seq)
             #:attr form '()
             #:with names #'()))
  
  (define-syntax-class unit-expr
    (pattern e
             #:with val #'e))

  
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
    (with-syntax ([(name ...) names])
      (tr:unit:local-table-property
       #'(let-values ((()
                       (list (cons (quote-syntax name) (lambda () name)) ...)))
           (void))
       #t))
    
    #;
    (tr:unit:local-table-property
     #`(let-values ([(#,@names)
                     (values #,@(map (lambda (stx) #`(lambda () (#,stx)))
                                     names))])
         (void))
     #t))
 
  (define (make-annotated-table names)
    (with-syntax ([(name ...) 
                   (map
                    (lambda (id)
                      (syntax-property id 'sig-id id))
                    names)])
      #`(let-values ((()
                      (begin 
                        (list name ...)
                        (values))))
          (void))))
  
  
  (define (make-unit-signature-table imports
                                     exports
                                     init-depends)
    
    #`(unit-internal 
       (#:imports #,@imports)
       (#:exports #,@exports)
       (#:init-depends #,@init-depends))))

(define-syntax (define-signature stx)
  (syntax-parse stx
    [(_ sig-name:id super-form:extends-form (form:def-sig-form ...))
     (ignore
      (quasisyntax/loc stx
        (begin
          #,(internal #'(define-signature-internal sig-name super-form.internal-form (form.internal-form ...)))
          (untyped-define-signature sig-name #,@(attribute super-form.form) (form.erased ...)))))]))


;; Could the local table mapping be represented as 
;; (let-values ((() (list id ...)) void)
;; with syntax-properties attached to each id that say the var it mapped from??
(define-syntax (add-tags stx)
  (syntax-parse stx
    [(add-tags e)
     (define e-stx (local-expand #'e
                                 (syntax-local-context)
                                 (append (kernel-form-identifier-list)
                                         (list (quote-syntax :)))))
     (syntax-parse e-stx
        #:literals (begin define-syntaxes define-values :)
        [(begin b ...) #'(add-tags b ...)]
        [(define-syntaxes (name:id ...) rhs:expr)
         e-stx]
        [(: var:id type)
         #`(let-values ([()
                         #,(tr:unit:annotation-property
                            #`(cons var (quote-syntax type)) 'ann)])
             (: var type)
             (void))]              ; maybe this should be (: var type) ???
        [(define-values (name:id ...) rhs:expr)
         (define names (syntax->list #'(name ...)))
         (define def-stx
           #`(define-values (name ...)
               #,(tr:unit:body-expr-or-annotation-property #'rhs
                                                           (syntax->list #'(name ...)))))
         ;; I think this should work it looks like the renamings are probably free-identifier=?
         ;; this way only need to deal with the names for the imports
         def-stx
         #;
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

(define-syntax (unit stx)
  (syntax-parse stx
    #:literals (import export)
    [(unit (import import-sig:id ...)
           (export export-sig:id ...)
           init-depends:init-depend-form
           e:unit-expr ...)
     (let ()
       (ignore
        (tr:unit
         (quasisyntax/loc stx
           (let-values ()
             #,(internal (make-unit-signature-table (syntax->list #`(import-sig ...))
                                                    (syntax->list #`(export-sig ...))
                                                    (syntax->list #`init-depends.names)))
             (untyped-unit  (import import-sig ...)
                            (export export-sig ...)
                            #,@(attribute init-depends.form)
                            #,(make-annotated-table (get-signatures-vars #'(import-sig ...)))
                            #,(make-locals-table
                               (get-signatures-vars #'(import-sig ...))
                               #;
                               (map
                               (lambda (id) (datum->syntax stx
                               (syntax->datum id)))
                               (get-signatures-vars #'(import-sig ...))))
                            (add-tags e ...)))))))]))
