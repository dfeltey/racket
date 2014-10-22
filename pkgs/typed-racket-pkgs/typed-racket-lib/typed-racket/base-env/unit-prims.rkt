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
                      (utils tc-utils)
                      syntax/id-table)
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
  
  
  ;; need lexical signature vars to error with duplicate type annotations
  (define (signatures-vars stx)
    (define (signature-vars sig-id)
      (let-values ([(_0 vars _2 _3)
                    (signature-members sig-id sig-id)])
        vars))
    (apply append (map signature-vars (syntax->list stx))))
  
  ;; extract vars from a signature with the correct syntax marks
  ;; I have no idea why this works, or is necessary
  ;; TODO: this is probably not general enough and will need to be modified
  ;; to deal with prefix/rename when those are implemented for TR units
  (define (get-signature-vars sig-id)
    (define-values (_0 vars _2 _3)
      ;; TODO: give better argument for error-stx
      (signature-members sig-id sig-id))

    (map
     (unitify-id sig-id)
     vars))
  
  ;; No idea what this does
  (define (unitify-id sig-id)
    (lambda (id)
      (syntax-local-introduce
       (syntax-local-get-shadower
        ((lambda (id-inner)
           (syntax-local-introduce
            ((syntax-local-make-delta-introducer sig-id) id-inner))) id)))))
  
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
          #,(internal 
             #'(define-signature-internal sig-name super-form.internal-form 
                 (form.internal-form ...)))
          (untyped-define-signature sig-name #,@(attribute super-form.form) 
                                    (form.erased ...)))))]))




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
#;
(define-syntax (add-tags stx)
  (define table (or (tr:unit:annotation-property stx) null))
  (define import-vars (or (tr:unit:sig-vars-property stx) null))
  (printf "import-vars: ~a\n" import-vars)
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
        ;(define test (syntax-local-value #'unit-info))
        (define a (first import-vars))
        ;(define intro (make-syntax-delta-introducer #'name a))
        (printf "name: ~a\n" #'name)
        (printf "a: ~a\n" a)
        (printf "(free-identifier=? name a) => ~a\n" 
                (free-identifier=? #'name 
                                   a))
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

;; start of rewrite to use define-syntax/syntax-local-value as a 
;; better communication channel inside the unit macro
;;
;; Also moving away from syntax properties as places to store type information
;; 2 Feautures to help fix this
;;   1. Indexing unit imports
;;   2. inserting define-values names into the expression needed to type check
;;


#;
(define-syntax (tag-unit-body-expr stx)
  (define (unit-expand stx)
    (local-expand stx 
                  (syntax-local-context)
                  (append (kernel-form-identifier-list (list (quote-syntax :))))))
  (syntax-parse stx
    [(_ unit-type-info:id e)
     (define exp-e (unit-expand #'e))
     (syntax-parse exp-e
       [(begin b ...)
        #`(begin
            (add-tags unit-type-info b) ...)]
       [(define-syntaxes (name:id ...) rhs:expr)
        #'(define-syntaxes (name ...) rhs)]
       [(define-values (name:id ...) rhs:expr)]
       [(: name:id type)]
       [_]
       
       )]))

(define-syntax (add-tags stx)
  (syntax-parse stx
    [(_) #'(begin)]
    [(_ e)
     (define exp-e (local-expand #'e (syntax-local-context) (kernel-form-identifier-list)))
     (syntax-parse exp-e
       #:literals (begin define-values define-syntaxes)
       [(begin b ...)
        #'(add-tags b ...)]
       [(define-syntaxes (name:id ...) rhs:expr) 
        exp-e]
       [(define-values (name:id ...) rhs)
        #`(define-values (name ...)
            #,(tr:unit:body-exp-def-type-property
               #'(#%expression
                  (begin
                    (void name ...)
                    rhs))
               'def/type))]
       [_
        (tr:unit:body-exp-def-type-property exp-e 'expr)])]
    [(_ e ...)
     #'(begin (add-tags e) ...)]))


#;
(define-syntax (add-tags stx)
  (define last-key (gensym))
  (syntax-parse stx
    [(_ unit-type-info:id) #'(begin)]
    
    #;
    [(_ unit-type-info:id e ... last)
     (define ctx (syntax-local-context))
     (define type-info (syntax-local-value #'unit-type-info))
     #`(begin 
         #,@(map (lambda (stx) (tag-unit-body-expr stx ctx #f)) (syntax->list #'(e ...)))
         #,(tag-unit-body-expr #'last ctx unit-type-info))]
    
        
    
    [(_ unit-type-info:id e ... last)
     #`(begin 
         (tag-unit-body-expr unit-type-info e) ...
         (finalize-typed-unit unit-type-info last))]
    
    #;
    [(add-tags) #'(begin)]
    #;
    [(add-tags f r ...)
     (define e-stx (unit-expand #'f))
     (syntax-parse e-stx
       #:literals (begin define-syntaxes define-values :)
       [(begin b ...) 
        #'(add-tags b ... r ...)]
       [(: name:id type)
        ;(define test (syntax-local-value #'unit-info))
        (define a (first import-vars))
        ;(define intro (make-syntax-delta-introducer #'name a))
        (printf "name: ~a\n" #'name)
        (printf "a: ~a\n" a)
        (printf "(free-identifier=? name a) => ~a\n" 
                (free-identifier=? #'name 
                                   a))
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


;; This table implementation is going to break when only/except are allowed in
;; typed units, the indexing strategy won't work in that case
(define-for-syntax (make-signature-local-table imports exports init-depends)
  (define (make-index-row sig-id)
    (with-syntax ([(sig-var ...) (get-signature-vars sig-id)]) 
      #`(list (quote-syntax #,sig-id) (cons (quote-syntax sig-var) (lambda () sig-var)) ...)))
  (tr:unit:index-table-property
   (with-syntax ([(init-depend ...) (syntax->list init-depends)])
     #`(let-values ([() (void #,@(map make-index-row (syntax->list imports)))]
                    [() (void #,@(map make-index-row (syntax->list exports)))]
                    [() (void (quote-syntax init-depend) ...)])
         (void)))
   #t))


(define-syntax (unit stx)
  (syntax-parse stx
    #:literals (import export)
    [(unit (import import-sig:id ...)
       (export export-sig:id ...)
       init-depends:init-depend-form
       e:unit-expr ...)
     (ignore
      (tr:unit
       (quasisyntax/loc stx
         ;; commenting this bit out since it now seems superflous and
         ;; I can keep all the necessary information inside the unit itself
         #;
         #,(internal (make-unit-signature-table (syntax->list #`(import-sig ...))
                                                (syntax->list #`(export-sig ...))
                                                (syntax->list #`init-depends.names)))
           (untyped-unit  (import import-sig ...)
                          (export export-sig ...)
                          #,@(attribute init-depends.form)
                          ;; Do I really need both of these table forms???
                          #|
                          #,(make-annotated-table (get-signatures-vars #'(import-sig ...)))
                          #,(make-locals-table
                          (get-signatures-vars #'(import-sig ...))
                          #;
                          (map
                          (lambda (id) (datum->syntax stx
                          (syntax->datum id)))
                          (get-signatures-vars #'(import-sig ...))))
                          |#
                          #,(make-signature-local-table #'(import-sig ...)
                                                        #'(export-sig ...)
                                                        #'init-depends.names)
                          (add-tags e ...)))))]))



