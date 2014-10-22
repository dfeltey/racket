#lang racket/unit

;; This module provides a unit for type-checking units

(require "../utils/utils.rkt"
         racket/dict
         racket/format
         racket/list
         racket/match
         racket/set
         racket/syntax
         syntax/id-table
         syntax/parse
         syntax/stx
         "signatures.rkt"
         (private parse-type syntax-properties type-annotation)
         (env lexical-env tvar-env global-env 
              signature-env signature-helper)
         (types utils abbrev union subtype resolve generalize)
         (typecheck check-below internal-forms)
         (utils tc-utils)
         (rep type-rep)
         (for-syntax racket/base)
         (for-template racket/base
                       (private unit-literals)
                       (typecheck internal-forms)))

;;  REMOVE LATER
(require racket/format
         racket/pretty)

(import tc-if^ tc-lambda^ tc-app^ tc-let^ tc-expr^)
(export check-unit^)

;; Syntax class deifnitions
;; variable annotations expand slightly differently in the body of a unit
;; due to how the unit macro transforms internal definitions
(define-syntax-class unit-body-annotation
  #:literal-sets (kernel-literals)
  #:literals (void values :-internal cons)
  (pattern
   (#%expression
    (begin 
      (#%plain-app void)
      (begin
        (quote-syntax
         (:-internal var:id t))
        (#%plain-app values))))
   #:attr name #'var
   #:attr type (parse-type #'t))
  ;; these 2 can probably be deleted
  #;
  (pattern (begin
             (quote-syntax
              (:-internal var:id expr))
             (#%plain-app values))
           #:with name #'var
           #:with type #'expr)
  #;
  (pattern (#%plain-app cons var:id (quote-syntax expr))
           #:with name #'var
           #:with type #'expr))

(struct sig-info (name externals internals) #:transparent)
;; A Sig-Info is a (sig-info identifier? (listof identifier?) (listof identifier?))
;; name is the identifier corresponding to the signature this sig-info represents
;; externals is the list of external names for variables in the signature
;; internals is the list of internal names for variables in the signature

(define-syntax-class unit-int-rep
  #:literal-sets (kernel-literals)
  (pattern (#%plain-app int-var:id)
           #:with id #'int-var)
  (pattern int-var:id
           #:with id #'int-var))

(define-syntax-class index-row
  #:literal-sets (kernel-literals)
  #:literals (list cons)
  (pattern 
   (#%plain-app list (quote-syntax sig-id:id) 
                (#%plain-app consx (quote-syntax var-ext:id) 
                             (#%plain-lambda () var-int:unit-int-rep)) ...)
   
   #:with name #'sig-id
   #:attr info (sig-info #'sig-id 
                         (syntax->list #'(var-ext ...)) 
                         (syntax->list #'(var-int.id ...)))))

(define (get-info stx)
  (syntax-parse stx
    [ir:index-row
     (attribute ir.info)]))

(define-syntax-class signature-index-table
  #:literal-sets (kernel-literals)
  #:literals (void list cons)
  (pattern
   (let-values ([() (#%plain-app void import:index-row ...)]
                [() (#%plain-app void export:index-row ...)]
                [() (#%plain-app void (quote-syntax init-depend:id) ...)])
     (#%plain-app void))
   #:attr imports (map get-info (syntax->list #'(import ...)))
   #:attr exports (map get-info (syntax->list #'(export ...)))
   #:attr init-depends (syntax->list #'(init-depend ...))))

(define (parse-index-table stx)
  (syntax-parse stx
    [t:signature-index-table
     (values (attribute t.imports)
             (attribute t.exports)
             (attribute t.init-depends))]))

(define-syntax-class unit-expansion
  #:literals (let-values letrec-syntaxes+values #%plain-app quote)
  #:attributes (;imports
                ;exports
                ;init-depends
                body-stx)
  (pattern (#%plain-app
            make-unit:id
            name:expr 
            import-vector:expr
            export-vector:expr
            list-dep:expr
            unit-body:expr)
           #:with body-stx #'unit-body))

;; Sig-Info -> (listof (pairof identifier? Type))
;; GIVEN: signature information
;; RETURNS: a mapping from internal names to types
(define (make-local-type-mapping si)
  (define sig (sig-info-name si))
  (define internal-names (sig-info-internals si))
  (define sig-types 
    (map (lambda (s) ((compose parse-type cdr) s)) (signature->bindings sig)))
  (map cons internal-names sig-types))

(define (arrowize-mapping mapping)
  (for/list ([(k v) (in-dict mapping)])
    (cons k (-> v))))

;; combine this and the above function later
(define (make-external-type-mapping si)
  (define sig (sig-info-name si))
  (define external-names (sig-info-externals si))
  (define sig-types 
    (map (lambda (s) ((compose parse-type cdr) s)) (signature->bindings sig)))
  (map cons external-names sig-types))

(define (lookup-type name mapping)
  (let ([v (assoc name mapping free-identifier=?)])
    (and v (cdr v))))


;; Syntax Option<TCResults> -> TCResults
;; Type-check a unit form
(define (check-unit form [expected #f])
  (define expected-type
    (match expected
      [(tc-result1: type) (resolve type)]
      [_ #f]))
  (match expected-type
    [(? Unit? unit-type)
     (ret (parse-and-check form unit-type))]
    [_ (ret (parse-and-check form #f))]))

(define (parse-and-check form expected)
  (syntax-parse form
    [u:unit-expansion
     (define body-stx #'u.body-stx)
     (define unit-index-table 
       (first (trawl-for-property body-stx tr:unit:index-table-property)))
     (define-values (imports-info exports-info init-depends)
       (parse-index-table unit-index-table))
     (printf "imports-info: ~a\n" imports-info)
     (printf "exports-info: ~a\n" exports-info)
     (printf "init-depends: ~a\n" init-depends)
     (define local-sig-type-map
       (apply append (map make-local-type-mapping imports-info)))
     (define signature-annotations
       (arrowize-mapping local-sig-type-map))
     (printf "signature-annotations: ~a\n" signature-annotations)
     
     (define external-sig-type-map
       (apply append (map make-external-type-mapping imports-info)))
     
     (printf "local-sig-type-map: ~a\n" local-sig-type-map)
     (define forms (trawl-for-property body-stx tr:unit:body-exp-def-type-property))
     (printf "forms: ~a\n" forms)
     
     (define annotations (filter unit-type-annotation? forms))
     (define forms-to-check (filter-not unit-type-annotation? forms))
     (printf "annotations: ~a\n" annotations)
     (define signature-names (apply append (map sig-info-externals imports-info)))
     (define annotation-map
       (for/fold ([mapping '()])
                 ([form (in-list annotations)])
         (syntax-parse form
           [ann:unit-body-annotation
            (define name (attribute ann.name))
            (define type (attribute ann.type))
            (printf "name: ~a\n" name)
            (printf "type: ~a\n" type)
            (cond
             [(or (member name (map car mapping) free-identifier=?)
                  (member name signature-names free-identifier=?))
              (tc-error/delayed #:stx name 
                                "Duplicate type annotation of ~a for ~a, previous was ~a"
                                type 
                                (syntax-e name) 
                                ;; FIXME: need to get the type from the mapping
                                ;; or from the signature depening on where the id
                                ;; came from
                                (or (lookup-type name mapping)
                                    (lookup-type name external-sig-type-map)))
              mapping]
             [else (cons (cons name type) mapping)])])))
     (define all-annotations (append annotation-map signature-annotations))
     (define body-type
       (with-lexical-env/extend 
           (map car all-annotations) (map cdr all-annotations)
           (for/last ([stx (in-list forms)])
             
               
               
               )))
     
     
     (printf "parsing ok!\n")
     
     (void)
     ])
  (make-Unit null null null -Void)
  )

(define (unit-type-annotation? stx)
  (syntax-parse stx
    [s:unit-body-annotation #t]
    [_ #f]))


;; Syntax Option<Type> -> Type
#;
(define (parse-and-check form expected)
  (syntax-parse form
    [u:unit-expansion
     (define body-stx #'u.body-stx)
     (define imports-stx (syntax->list #'u.imports))
     (define imports (map lookup-signature imports-stx))
     (define exports-stx (syntax->list #'u.exports))
     (define exports (map lookup-signature exports-stx))
     (define init-depends (map lookup-signature (syntax->list #'u.init-depends)))
     (define import-mapping (signatures->bindings imports-stx))
     (define export-mapping (signatures->bindings exports-stx))
          
     (define exprs+defns 
       (trawl-for-property body-stx tr:unit:body-expr-or-defn-property))
     
     (define defns (filter list?
                           (map tr:unit:body-expr-or-defn-property exprs+defns)))
     
     (printf "defns: ~a\n" defns)
     #;
     (define-values (bad-anns exprs+defns)
       (split-annotations exprs+annotations))
     
     (define local-table-stx
       (first (trawl-for-property body-stx tr:unit:local-table-property)))
     (define local-names-stxs
       (trawl-for-property body-stx (lambda (stx) (syntax-property stx 'sig-id))))
     (define local-name-mapping (parse-local-names local-names-stxs))
     
     (define anns
       (map tr:unit:annotation-property
            (trawl-for-property body-stx tr:unit:annotation-property)))
     
     (define body-annotations (if (empty? anns) empty (last anns)))
     
     (define b-type (car (first body-annotations)))
     (define b-def (first (first defns)))
     (printf "b-type: ~a\nb-def: ~a\n" b-type b-type)
     (printf "(free-identifier=? b-type b-def) => ~a\n" (free-identifier=? b-type b-def))
     
     
     
     
     (printf "anns: ~a\n" anns)
     
     ;; check that no annotation for unit variables are defined
     (define import-names (map (lambda (stx) (syntax-property stx 'sig-id)) local-names-stxs))
     (printf "local-names: ~a\n" import-names)
     ;; 
     
     (printf "body-annotations ~a\n" body-annotations)
     ;(define a-body (car (first body-annotations)))
     ;(define a-sig (first import-names))
     ;(printf "a-body: ~a\n" a-body)
     ;(printf "a-sig: ~a\n" a-sig)
     
     #;
     (for ([name import-names])
       (define ref (assoc name body-annotations free-identifier=?))
       (when ref
         (tc-error/delayed #:stx (car ref)
                           "Duplicate type annotation of ~a for ~a, previous was ~a"
                           (syntax-e (cdr ref))
                           (syntax-e (car ref))
                           'PLACEHOLDER)))
     
     
 
     (define-values (local-names local-types)
       (let ([local-dict (compose-mappings local-name-mapping import-mapping)])
         (for/fold ([names '()]
                    [types '()])
                   ([(k v) (in-dict local-dict)])
           (values (cons k names) (cons (-> (parse-type v)) types)))))
     
     (define body-type #f)
     #;
     (define body-type
       (with-lexical-env/extend 
           (append local-names (map car anns)) (append local-types (map cdr anns)) 
           (for/last ([stx (in-list (reverse exprs+defns))])
             (define prop-val (tr:unit:body-expr-or-defn-property stx))
             (define results (tc-expr stx))
             (define types (tc-results-ts results))
             
             (cond
              ;; syntax came from a definition need to check subtyping here
              ;; be careful about defs for exported sigs
              [(list? prop-val) 
               (cond [(empty? prop-val) -Void]
                     [else
                      (define var-types (map
                                         (lambda (id)
                                           (or (ref anns id)
                                               (let ([ty (ref export-mapping id)])
                                                 (or (and ty (parse-type ty)) Univ))))
                                         prop-val))
                      
                      
                      (printf "anns: ~a\n" anns)
                      
                      (printf "(bound-identifier=? (car prop-val) (car (car anns))): ~a\n"
                              (bound-identifier=? (car prop-val) (car (car anns)) #f))
                      #|
                      ;(printf "prop-val: ~a\n" prop-val)
                      ;(printf "anns: ~a\n" anns)
                      ;(printf "(car prop-val): ~a\n" (car prop-val))
                      ;(printf "(ref anns (car prop-val)): ~a\n" (ref anns (car prop-val)))
                      ;(printf "var-types: ~a\n" var-types)
                      (printf "Inspect Syntax prop-val\n")
                      (for ([id prop-val])
                        (inspect-syntax id))
                      (printf "Inspect Syntax anns\n")
                      (for ([(id type) (in-dict anns)])
                        (inspect-syntax id))
                      
                      
                      
                      (printf "anns c -> ~a\n" (identifier-binding-symbol (car (car anns))))
                      (printf "prop-val c -> ~a\n" (identifier-binding-symbol (car prop-val)))
                      (printf "werid=?: ~a\n" (weird=? (car prop-val) (car (car anns))))
                      (define ac (car (car anns)))
                      (define pvc (car prop-val))
                      (printf "id-bind ac ~a\n" (identifier-binding ac))
                      (printf "id-bind pvc ~a\n" (identifier-binding pvc))
                      |#
                      
                      
                      (check-below results (ret var-types))
                      -Void])]
              [else (first types)])
             
             )))
     (define unit-type (or body-type -Void))
     (make-Unit imports exports init-depends unit-type)
     ]))

(define (ann->dict stxs)
  (for/list ([stx stxs])
    (syntax-parse stx
      [:unit-body-annotation
       (cons #'name (parse-type #'type))])))

(define (parse-local-names stxs)
  (for/list ([stx stxs])
    (syntax-parse stx
      #:literals (#%plain-app)
      [(#%plain-app name:id)
       (cons #'name (syntax-property stx 'sig-id))])))

;; (Listof Syntax) -> (Values (Listof (Pairof Identifier Type) (Listof Syntax))
;; GIVEN: a list of syntax representing definition expressions and
;;        annotation expressions found within a unit
;; WHERE: each element in the list of syntax has the 
;;        tr:unit:body-expr-or-defn syntax-property
;; RETURNS: two lists, the first contains all the annotations from 
;;          the unit body, and the second only the expressions
;;          the returned lists are in reverse order of their position
;;          from the unit body
#;
(define (split-annotations stxs)
  (for/fold ([anns '()]
             [exprs '()])
            ([stx (in-list stxs)])
    (define prop-val (tr:unit:body-expr-or-defn-property stx))
    (if (list? prop-val)
        (syntax-parse stx
          [e:unit-body-annotation
           (define ann (cons #'e.name (parse-type #'e.type)))
           (values (cons ann anns) exprs)]
          [_ 
           (values anns (cons stx exprs))])
        (values anns (cons stx exprs)))))


(define (ref dict id)
  (let ([val (assoc id dict free-identifier=?)])
    (if val (cdr val) #f)))

;; AList AList -> AList
;; GIVEN: two association lists
;; RETURNS: their composition
(define (compose-mappings m1 m2)
  (for/list ([kv (in-list m1)])
    (define key (car kv))
    (define val (cdr kv))
    (cons key
          ;; would be nice to make this an arrow type
          ;; and parse it here instead of above ...
          (cdr (assoc val m2 free-identifier=?)))))


;; copied from check-class-unit.rkt
;; Syntax (Syntax -> Any) -> Listof<Syntax>
;; Look through the expansion of the unit macro in search for
;; syntax with some property (e.g., definition bodies and expressions)
(define (trawl-for-property form accessor)
  (define (recur-on-all stx-list)
    (apply append (map (λ (stx) (trawl-for-property stx accessor))
                       (syntax->list stx-list))))
  (syntax-parse form
    #:literals (let-values letrec-values #%plain-app
                #%plain-lambda letrec-syntaxes+values
                #%expression begin)
    [stx
     #:when (accessor #'stx)
     (list form)]
    [(let-values (b ...) body ...)
     (recur-on-all #'(b ... body ...))]
    ;; for letrecs, traverse the RHSs too
    [(letrec-values ([(x ...) rhs ...] ...) body ...)
     (recur-on-all #'(rhs ... ... body ...))]
    [(letrec-syntaxes+values (sb ...) ([(x ...) rhs ...] ...) body ...)
     (recur-on-all #'(rhs ... ... body ...))]
    [(#%plain-app e ...)
     (recur-on-all #'(e ...))]
    [(#%plain-lambda (x ...) e ...)
     (recur-on-all #'(e ...))]
    [(begin e ...)
     (recur-on-all #'(e ...))]
    [(#%expression e)
     (recur-on-all #'e)]
    [(() e)
     (recur-on-all #'(e))]
    [_ '()]))



;;;;;;;;; REMOVE THIS LATER

(define (weird=? id1 id2)
  (equal?
   (identifier-binding-symbol id1)
   (identifier-binding-symbol id2)))



;; This module provides utility functions for examining syntax objects
(define rule (make-string 50 #\;))
(define (prule) (displayln rule))
(define (inspect-syntax stx)
  (define datum (syntax->datum stx))
  (define keys (syntax-property-symbol-keys stx))
  (prule)
  (displayln (~a ";; Inspecting syntax object: " (~a stx #:max-width 20)))
  (newline)
  (displayln "Pretty-printed syntax:")
  (pretty-print datum)
  (newline)
  (displayln (~a "Source: " (~a #:width 20 #:align 'right (syntax-source stx))))
  (displayln (~a "Line: " (~a #:width 22 #:align 'right (syntax-line stx))))
  (displayln (~a "Column: " (~a #:width 20 #:align 'right (syntax-column stx))))
  (displayln (~a "Position: " (~a #:width 18 #:align 'right (syntax-position stx))))
  (displayln (~a "Span: " (~a #:width 22 #:align 'right (syntax-span stx))))
  (newline)
  (displayln "Properties:")
  (for ([key (in-list keys)])
    (displayln (~a " " key ": " (syntax-property stx key))))
  (newline)
  (newline)
  (displayln (~a "Tainted: " (~a #:width 19 #:align 'right (syntax-tainted? stx))))
  (newline)
  (prule))
