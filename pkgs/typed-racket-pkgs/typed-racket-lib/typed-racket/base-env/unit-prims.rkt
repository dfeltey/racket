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
                      syntax/strip-context
                      (utils tc-utils))
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




;; helpful definitions for later typechecking
(define-values-for-syntax (access-table add-table)
  (let* ([key (gensym)]
         [get-table (lambda (stx) (syntax-property stx key))]
         [set-table (lambda (stx table) (syntax-property stx key table))])
    (values get-table set-table)))

(define-for-syntax (type-table-ref table id)
  (assoc id table free-identifier=?))

;; LIMITATION: Type annotations must appear before the 
;;             variable they reference is defined
;; NOTE: I think the above limitation is fixed, by adding the 
;; annotation property to every piece of syntax encountered by
;; the add-tags macro in a place that the unit macro will
;; leave intact
;; then it just requires getting the table from the last body expr
;; that had the annotation property
(define-syntax (add-tags stx)
  (define table (or (tr:unit:annotation-property stx) null))
  (define (unit-expand stx)
    (local-expand stx 
                  (syntax-local-context) 
                  (append (kernel-form-identifier-list)
                          (list (quote-syntax :)))))
  (syntax-parse stx
    [(add-tags) #'(begin)]
    [(add-tags f r ...)
     (define e-stx (unit-expand #'f))
     (syntax-parse e-stx
       #:literals (begin define-syntaxes define-values :)
       [(begin b ...) 
        #'(add-tags b ... r ...)]
       [(: name:id type)
        (when (type-table-ref table #'name)
          (tc-error/delayed #:stx #'name 
                            "Duplicate type annotation of ~a for ~a, previous was ~a"
                            (syntax-e #'type)
                            (syntax-e #'name)
                            (syntax-e (cdr (type-table-ref table #'name)))))
        #`(begin
            (: name type)
            #,(tr:unit:annotation-property #'(add-tags r ...) (cons #'name #'type)))]
       [(define-syntaxes (name:id ...) rhs:expr)
        #`(begin 
            (define-syntaxes (name ...) rhs)
            (add-tags r ...))]
       [(define-values (name:id ...) rhs:expr)
        #`(begin
            (define-values (name ...)
              #,(tr:unit:annotation-property 
                 (tr:unit:body-expr-or-defn-property
                  #'rhs 
                  (syntax->list #'(name ...)))
                 table))
            (add-tags r ...))]
       [_
        #`(begin
            #,(tr:unit:body-expr-or-defn-property e-stx 'expr)
            (add-tags r ...))])]))

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
                            #,(tr:unit:annotation-property #'(add-tags e ...) null)))))))]))
