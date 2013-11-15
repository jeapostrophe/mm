#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         "ast.rkt"
         "id-table.rkt"
         racket/bool
         racket/list)

;; Mutator Source Language (Scheme-like) compiler to use allocator
(begin-for-syntax
  (require syntax/id-table
           racket/dict
           "id-table.rkt")

  (define mutator-macros (make-free-id-table))

  (define-syntax-class mutator-macro
    #:commit
    #:attributes (expander)
    (pattern m:id
             #:fail-unless
             (dict-has-key? mutator-macros #'m)
             "mutator macro"
             #:attr expander
             (dict-ref mutator-macros #'m))))

(define-syntax (define-mutator-macro stx)
  (syntax-parse stx
    [(_ (id stx-id) body)
     (syntax/loc stx
       (begin-for-syntax
         (dict-set! mutator-macros #'id
                    (λ (stx-id) body))))]))

(define-mutator-macro (test stx)
  (syntax-parse stx
    [(_ lhs rhs)
     (syntax/loc stx
       (let ([lhs-v lhs] [rhs-v rhs])
         (unless (equal? lhs-v rhs-v)
           (error 'test "not equal: ~e and ~e" lhs-v rhs-v))))]))

(define-mutator-macro (and stx)
  (syntax-parse stx
    [(_)
     (syntax/loc stx #t)]
    [(_ e)
     (syntax/loc stx e)]
    [(_ e . more)
     (syntax/loc stx (if e (and . more) #f))]))

(define-mutator-macro (when stx)
  (syntax-parse stx
    [(_ t . b)
     (syntax/loc stx
       (if t (let () . b) (void)))]))

(define-mutator-macro (unless stx)
  (syntax-parse stx
    [(_ t . b)
     (syntax/loc stx
       (when (not t) . b))]))

(define-mutator-macro (or stx)
  (syntax-parse stx
    [(_)
     (syntax/loc stx #f)]
    [(_ e)
     (syntax/loc stx e)]
    [(_ e . more)
     (syntax/loc stx (let ([t e]) (if t t (or . more))))]))

(define-mutator-macro (cond stx)
  (syntax-parse stx
    [(cond)
     (syntax/loc stx
       (void))]
    [(cond [(~literal else) . b])
     (syntax/loc stx
       (let () . b))]
    [(cond [c . b] . more)
     (syntax/loc stx
       (if c
         (let () . b)
         (cond . more)))]))

(define-mutator-macro (quote stx)
  (syntax-parse stx
    [(_ ())
     (syntax/loc stx
       empty)]
    [(_ (f . r))
     (syntax/loc stx
       (cons (quote f) (quote r)))]
    [(_ n:number)
     (syntax/loc stx
       n)]
    [(_ b:boolean)
     (syntax/loc stx
       b)]))

(define-mutator-macro (begin stx)
  (syntax-parse stx
    [(_)
     (syntax/loc stx (void))]
    [(_ e)
     (syntax/loc stx e)]
    [(_ fst more ...)
     (syntax/loc stx
       (let ([ignored fst]) (begin more ...)))]))

(define-mutator-macro (let stx)
  (syntax-parse stx
    [(_ () bb)
     (syntax/loc stx
       bb)]
    [(_ ([b be] ...) . bb)
     (syntax/loc stx
       ((λ (b ...) . bb) be ...))]))

(define-mutator-macro (let* stx)
  (syntax-parse stx
    [(_ () . bb)
     (syntax/loc stx
       (let () . bb))]
    [(_ ([b be] . more) . bb)
     (syntax/loc stx
       (let ([b be])
         (let* more . bb)))]))

(define-mutator-macro (letrec stx)
  (syntax-parse stx
    [(_ ([b be] ...) . bb)
     (syntax/loc stx
       (let ([b (box 42)] ...)
         (begin (set-box! b (Mr.Gorbachev-unbox-these-identifiers!
                             (b ...)
                             be))
                ...
                (Mr.Gorbachev-unbox-these-identifiers!
                 (b ...)
                 (let () . bb)))))]))

(define-syntax (Mr.Gorbachev-unbox-these-identifiers! stx)
  (raise-syntax-error 'Mr.Gorbachev-unbox-these-identifiers!
                      "Illegal outside mutator" stx))

(begin-for-syntax
  (define mutator-lifted-primitives
    (list->id-set #'(+ - * / add1 sub1 empty? even? odd? = < > <= >= zero?
                       not error printf symbol=? string=? number? boolean?)))
  (define mutator-primitives
    (id-set
     ;; Normal
     [eq? address=?]
     [equal? mutator-equal?]
     [box? box?]
     [unbox box-deref]
     [set-box! box-set!]
     [cons? cons?]
     [first cons-first]
     [rest cons-rest]
     [set-first! cons-set-first!]
     [set-rest! cons-set-rest!]
     [car cons-first]
     [cdr cons-rest]
     [set-car! cons-set-first!]
     [set-cdr! cons-set-rest!]
     ;; CPS
     [box box-allocate]
     [cons cons-allocate]))

  (define-syntax-class mutator-primitive
    #:commit
    #:attributes (rewrite)
    (pattern x:id
             #:do [(define r (dict-ref mutator-primitives #'x #f))]
             #:when r
             #:attr rewrite #`(quote #,r))
    (pattern x:id
             #:do [(define r (dict-ref mutator-lifted-primitives #'x #f))]
             #:when r
             #:attr rewrite #'x))

  (define-syntax-class mutator-keyword
    (pattern (~or (~literal if)
                  (~literal Mr.Gorbachev-unbox-these-identifiers!)
                  p:mutator-primitive
                  (~literal λ)
                  (~literal empty) (~literal void) (~literal define)
                  m:mutator-macro)))

  (define-syntax-class (mutator-expr ubs)
    #:commit
    #:attributes (stx)
    (pattern ((~literal Mr.Gorbachev-unbox-these-identifiers!)
              (x:id ...) e)
             #:declare e (mutator-expr
                          (for/fold ([ubs ubs])
                              ([x (in-list (syntax->list #'(x ...)))])
                            (dict-set ubs x #t)))
             #:attr stx (attribute e.stx))
    (pattern ((~literal if)
              (~var c (mutator-expr ubs))
              (~var t (mutator-expr ubs))
              (~var f (mutator-expr ubs)))
             #:attr stx
             (quasisyntax/loc this-syntax
               (mutator-if c.stx t.stx f.stx)))
    (pattern (prim:mutator-primitive (~var arg (mutator-expr ubs)) ...)
             #:attr stx
             (syntax/loc this-syntax
               (mutator-primitive prim.rewrite (list arg.stx ...))))
    (pattern ((~literal λ) (x:id ...)
              (~var p (mutator-program ubs)))
             #:attr stx
             (syntax/loc this-syntax
               (mutator-lambda (list #'x ...) p.stx)))
    (pattern (~or x:number x:boolean x:str (~and x ((~literal quote) y:id))
                  (~and x (~literal empty))
                  (~and x ((~literal void))))
             #:attr stx
             (syntax/loc this-syntax
               (mutator-atomic x)))
    (pattern x:identifier
             #:attr stx
             (if (dict-ref ubs #'x #f)
               (let ()
                 (define/syntax-parse
                   (~var ux (mutator-expr (dict-remove ubs #'x)))
                   (syntax/loc this-syntax
                     (unbox x)))
                 (attribute ux.stx))
               (syntax/loc this-syntax
                 (mutator-id #'x))))
    (pattern (m:mutator-macro . body)
             #:with mac-out ((attribute m.expander) this-syntax)
             #:with (~var e (mutator-expr ubs)) #'mac-out
             #:attr stx #'e.stx)
    (pattern ((~and (~not x:mutator-keyword)
                    (~var fun (mutator-expr ubs)))
              (~var arg (mutator-expr ubs)) ...)
             #:attr stx
             (syntax/loc this-syntax
               (mutator-apply fun.stx (list arg.stx ...)))))

  (define-syntax-class mutator-define
    #:commit
    #:attributes (id body)
    (pattern ((~literal define) x:id e)
             #:attr id #'x
             #:attr body #'e)
    (pattern ((~literal define) (x:id arg:id ...) . e)
             #:attr id #'x
             #:attr body
             (syntax/loc this-syntax
               (λ (arg ...) . e))))

  (define-splicing-syntax-class (mutator-program ubs)
    #:commit
    #:attributes (stx)
    (pattern (~seq d:mutator-define ...+ p ...)
             #:with (~var b (mutator-expr ubs))
             (syntax/loc this-syntax
               (letrec ([d.id d.body] ...) p ...))
             #:attr stx #'b.stx)
    (pattern (~seq e p ...+)
             #:with (~var b (mutator-expr ubs))
             (syntax/loc #'e
               (let ([ignored e]) p ...))
             #:attr stx #'b.stx)
    (pattern (~seq e)
             #:with (~var b (mutator-expr ubs)) #'e
             #:attr stx #'b.stx)))

(define-syntax (mutator stx)
  (syntax-parse stx
    [(_ . p)
     #:with ((~var m (mutator-program empty-id-table))) #'p
     (syntax/loc stx
       m.stx)]))

(provide mutator)
