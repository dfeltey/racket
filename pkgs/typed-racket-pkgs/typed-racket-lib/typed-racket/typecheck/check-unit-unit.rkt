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
  #:literals (values :-internal cons)
  (pattern (begin
             (quote-syntax
              (:-internal var:id expr))
             (#%plain-app values))
           #:with name #'var
           #:with type #'expr)
  (pattern (#%plain-app cons var:id (quote-syntax expr))
           #:with name #'var
           #:with type #'expr))

(define-syntax-class unit-local-table
  #:literal-sets (kernel-literals)
  #:literals (values list cons)
  (pattern 
   (let-values (((ext-id:id ...)
                 (#%plain-app
                  values
                  (#%plain-lambda () (#%plain-app (#%plain-app local-id:id))) ...))
                ...)
     (#%plain-app void))
   #:with external-names #'(ext-id ... ...)
   #:with internal-names #'(local-id ... ...))
  (pattern 
   (let-values ((()
                 (#%plain-app 
                  list
                  (#%plain-app
                   cons
                   (quote-syntax var:id)
                   (#%plain-lambda () (#%plain-app local-name:id))) ...)))
     (#%plain-app void))
   #:with external-names #'(var ...)
   #:with internal-names #'(local-name ...)))

(define-syntax-class internal-unit-data
  #:literal-sets (kernel-literals)
  #:literals (unit-internal values)
  (pattern (begin (quote-syntax
                   (unit-internal
                    (#:imports import-sig:id ...)
                    (#:exports export-sig:id ...)
                    (#:init-depends init-dep-sig:id ...)))                  
                  (#%plain-app values))
           #:with imports #'(import-sig ...)
           #:with exports #'(export-sig ...)
           #:with init-depends #'(init-dep-sig ...)))

(define-syntax-class unit-expansion
  #:literals (let-values letrec-syntaxes+values #%plain-app quote)
  #:attributes (imports
                exports
                init-depends
                body-stx)
  (pattern (let-values ()
             (letrec-syntaxes+values 
              ()
              ((()
                :internal-unit-data))
              (#%plain-app
               make-unit:id
               name:expr 
               import-vector:expr
               export-vector:expr
               list-dep:expr
               unit-body:expr)))
           #:with body-stx #'unit-body))



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

;; Syntax Option<Type> -> Type
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
     (printf "Body: ~a\n" exprs+defns)
     #;
     (define-values (bad-anns exprs+defns)
       (split-annotations exprs+annotations))
     #;
     (define anns
       (ann->dict (trawl-for-property body-stx tr:unit:annotation-property)))
     
     (define local-table-stx
       (first (trawl-for-property body-stx tr:unit:local-table-property)))
     
     (define local-names-stxs
       (trawl-for-property body-stx (lambda (stx) (syntax-property stx 'sig-id))))
     (define local-name-mapping (parse-local-names local-names-stxs))
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

;; assuming the stx is actually a valid local table
(define (parse-local-table-mapping stx)
  (syntax-parse stx
    [e:unit-local-table
     (define external-names (syntax->list #'e.external-names))
     (define internal-names (syntax->list #'e.internal-names))
     (map cons internal-names external-names)]))

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
