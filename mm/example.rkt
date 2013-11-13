#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/list
                     racket/syntax)
         (prefix-in racket: racket/base)
         racket/bool
         racket/stxparam
         (except-in racket/list cons?))

;; Mutator Source Language (Scheme-like) compiler to use allocator
(begin-for-syntax
  (require syntax/id-table
           racket/dict)
  (define empty-id-table (make-immutable-free-id-table empty))
  (define-syntax-rule (id-set [k v] ...)
    (make-immutable-free-id-table (list (cons #'k #'v) ...)))

  (define (list->id-set ks)
    (for/fold ([ids empty-id-table])
        ([k (in-list (if (syntax? ks) (syntax->list ks) ks))])
      (dict-set ids k #t)))
  (define (id-set-union ids-l)
    (for*/fold ([all-ids empty-id-table])
        ([next-ids (in-list ids-l)]
         [next-id (in-dict-keys next-ids)])
      (dict-set all-ids next-id #t)))
  (define (id-set->list ids)
    (for/list ([k (in-dict-keys ids)])
      k))
  (define (id-set-remove ids lst)
    (for/fold ([ids ids])
        ([k (in-list (if (syntax? lst) (syntax->list lst) lst))])
      (dict-remove ids k)))

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

  (define-syntax-class mutator-lifted-primitive
    #:commit
    (pattern x:id
             #:when (dict-ref mutator-lifted-primitives #'x #f)))

  (define mutator-primitives
    (id-set [eq? address=?]
            [equal? mutator-equal?]
            [box? box?]
            [unbox box-deref]
            [box box-allocate]
            [set-box! box-set!]
            [cons? cons?]
            [cons cons-allocate]
            [first cons-first]
            [rest cons-rest]
            [set-first! con-set-first!]
            [set-rest! con-set-rest!]
            [car cons-first]
            [cdr cons-rest]
            [set-car! con-set-first!]
            [set-cdr! con-set-rest!]))
  (define-syntax-class mutator-primitive
    #:commit
    #:attributes (rewrite)
    (pattern x:id
             #:do [(define r (dict-ref mutator-primitives #'x #f))]
             #:when r
             #:attr rewrite r))

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
               (if c.stx t.stx f.stx)))
    (pattern (prim:mutator-lifted-primitive
              (~var arg (mutator-expr ubs)) ...)
             #:attr stx
             (syntax/loc this-syntax
               (atomic-allocate (prim (atomic-deref arg.stx) ...))))
    (pattern (prim:mutator-primitive
              (~var arg (mutator-expr ubs)) ...)
             #:attr stx
             (syntax/loc this-syntax
               (prim.rewrite arg.stx ...)))
    (pattern ((~literal λ) (x:id ...)
              (~var p (mutator-program ubs)))
             #:attr stx
             (syntax/loc this-syntax
               (λ (x ...) p.stx)))
    (pattern (~literal empty)
             #:attr stx
             (syntax/loc this-syntax
               (atomic-allocate empty)))
    (pattern ((~literal void))
             #:attr stx
             (syntax/loc this-syntax
               (atomic-allocate (void))))
    (pattern x:identifier
             #:attr stx
             (if (dict-ref ubs #'x #f)
               (let ()
                 (define/syntax-parse
                   (~var ux (mutator-expr (dict-remove ubs #'x)))
                   (syntax/loc this-syntax
                     (unbox x)))
                 (attribute ux.stx))
               #'x))
    (pattern (~or x:number x:boolean x:str (~and x ((~literal quote) y:id)))
             #:attr stx
             (syntax/loc this-syntax
               (atomic-allocate x)))
    (pattern (m:mutator-macro . body)
             #:with (~var e (mutator-expr ubs)) ((attribute m.expander) this-syntax)
             #:attr stx #'e.stx)
    (pattern ((~and (~not (~or (~literal if)
                               p:mutator-primitive p:mutator-lifted-primitive
                               (~literal λ)
                               (~literal empty) (~literal void) (~literal define)
                               m:mutator-macro))
                    (~var fun (mutator-expr ubs)))
              (~var arg (mutator-expr ubs))
              ...)
             #:attr stx
             (syntax/loc this-syntax
               (fun.stx arg.stx ...))))

  (define-splicing-syntax-class (mutator-program ubs)
    #:commit
    #:attributes (stx)
    (pattern (~seq ((~literal define) x:id e) p ...)
             #:with (~var b (mutator-expr ubs))
             (syntax/loc #'x
               (letrec ([x e]) p ...))
             #:attr stx #'b.stx)
    (pattern (~seq ((~literal define) (x:id arg:id ...) . e) p ...)
             #:with ((~var b (mutator-program ubs)))
             (syntax/loc #'x
               ((define x (λ (arg ...) . e)) p ...))
             #:attr stx #'b.stx)
    (pattern (~seq e p ...)
             #:with (~var b (mutator-expr ubs))
             (syntax/loc #'e
               (let ([ignored e]) p ...))
             #:attr stx #'b.stx)
    (pattern (~seq e)
             #:with (~var b (mutator-expr ubs)) #'e
             #:attr stx #'b.stx)))

;; CPS Transform for mutator language compilation output
(begin-for-syntax
  (define-syntax-class cps-atom
    #:attributes (ids)
    #:commit
    (pattern x:id
             #:attr ids (list #'x))
    (pattern (~or n:number b:boolean s:str ((~literal quote) x:id))
             #:attr ids empty)
    (pattern (~literal empty)
             #:attr ids (list #'empty))
    (pattern ((~literal void))
             #:attr ids (list #'void)))

  (define-syntax-class (cps-expr k)
    #:commit
    #:attributes (stx)
    (pattern ((~literal λ) (arg:id ...) body)
             #:with dyn-k (generate-temporary 'λ-k)
             #:with (~var cps-body (cps-expr #'dyn-k)) #'body
             #:attr stx
             (quasisyntax/loc this-syntax
               (#,k
                (λ (arg ... dyn-k)
                  cps-body.stx))))
    (pattern ((~literal if) c t f)
             #:with if-k (generate-temporary 'if-k)
             #:with (~var cps-c (cps-expr #'if-k)) #'c
             #:with (~var cps-t (cps-expr k)) #'t
             #:with (~var cps-f (cps-expr k)) #'f
             #:attr stx
             (syntax/loc this-syntax
               ((λ (if-k) cps-c.stx)
                (λ (c-id)
                  (if c-id
                    cps-t.stx
                    cps-f.stx)))))
    (pattern x:id
             #:attr stx
             (quasisyntax/loc this-syntax
               (#,k x)))
    (pattern (fun:mutator-lifted-primitive arg:cps-atom ...)
             #:attr stx
             (quasisyntax/loc this-syntax
               (#,k (fun arg ...))))
    (pattern (fun:cps-atom arg:cps-atom ...)
             #:attr stx
             (quasisyntax/loc this-syntax
               (fun arg ... #,k)))
    (pattern (before:cps-atom ... middle:expr after ...)
             #:with middle-k (generate-temporary 'app-k)
             #:with (~var cps-middle (cps-expr #'middle-k)) #'middle
             #:with middle-id (generate-temporary 'app-id)
             #:with (~var cps-b (cps-expr k))
             (syntax/loc this-syntax
               (before ... middle-id after ...))
             #:attr stx
             (quasisyntax/loc this-syntax
               (#,(quasisyntax/loc this-syntax
                    (λ (middle-k) cps-middle.stx))
                #,(quasisyntax/loc this-syntax
                    (λ (middle-id) cps-b.stx)))))))

;; Lambda lifting and closure conversion for cps output
(begin-for-syntax
  (define lift-globals
    (id-set-union
     (list
      mutator-lifted-primitives
      mutator-primitives
      (list->id-set
       #'(stack-exit atomic-allocate atomic-deref empty void)))))

  (define-syntax-class lift-expr
    #:attributes (stx lambdas ids)
    (pattern ((~literal λ) (x:id ...) body:lift-expr)
             #:with λ-id (generate-temporary 'λ-id)
             #:attr ids (id-set-remove (attribute body.ids) #'(λ-id x ...))
             #:with (fv ...) (id-set->list (attribute ids))
             #:attr lambdas
             #`([λ-id
                 #,(quasisyntax/loc this-syntax
                     (λ (fv ...)
                       #,(quasisyntax/loc this-syntax
                           (λ (x ...) body.stx))))]
                . body.lambdas)
             #:attr stx
             (syntax/loc this-syntax
               (closure-allocate λ-id (list fv ...))))
    (pattern ((~literal if) ca:cps-atom t:lift-expr f:lift-expr)
             #:attr ids
             (id-set-union
              (list
               (id-set-remove
                (list->id-set (attribute ca.ids))
                (id-set->list lift-globals))
               (attribute t.ids)
               (attribute f.ids)))
             #:with (t-l ...) #'t.lambdas
             #:with (f-l ...) #'f.lambdas
             #:attr lambdas
             #'(t-l ... f-l ...)
             #:attr stx
             (syntax/loc this-syntax
               (if ca t.stx f.stx)))
    (pattern x:cps-atom
             #:attr ids
             (id-set-remove
              (list->id-set (attribute x.ids))
              (id-set->list lift-globals))
             #:attr lambdas #'()
             #:attr stx this-syntax)
    (pattern (kont-user:lift-expr kont:lift-expr ...)
             #:attr ids
             (id-set-union (cons (attribute kont-user.ids)
                                 (attribute kont.ids)))
             #:with (ku-l ...) #'kont-user.lambdas
             #:with ((k-l ...) ...) #'(kont.lambdas ...)
             #:attr lambdas #'(ku-l ... k-l ... ...)
             #:attr stx
             (syntax/loc this-syntax
               (closure-apply kont-user.stx kont.stx ...)))))

(require racket/pretty)
(define-syntax (mutator stx)
  (syntax-parse stx
    [(_ . p)
     #:with ((~var m (mutator-program empty-id-table))) #'p
     #:with (~var c (cps-expr #'stack-exit)) #'m.stx
     #:with l:lift-expr #'c.stx
     #:with l-output #'(letrec l.lambdas
                         (initialize)
                         l.stx)
     (syntax/loc stx
       (begin
         ;; (pretty-print '(raw: p))
         ;; (pretty-print '(mutator: m.stx))
         ;; (pretty-print '(cps: c.stx))
         ;; (pretty-print '(lift: l-output))
         l-output))]))

(define (stack-exit v)
  v)
;; xxx allocate?
(define (address=? x y k)
  (closure-apply k (= x y)))
;; xxx allocate?
(define (mutator-equal? x y k)
  ;; xxx really should walk these pointers
  (closure-apply k (equal? x y)))

;; Uses
(struct clo (code-ptr free-vars) #:transparent)

(define (closure-apply c . args)
  (if (clo? c)
    (apply
     (apply (clo-code-ptr c)
            (clo-free-vars c))
     args)
    (apply c args)))

(define (initialize)
  (void))

(define (closure-allocate f fvs)
  (clo f fvs))

(define (atomic-allocate x k)
  (closure-apply k x))
(define (atomic-deref x k)
  (closure-apply k x))

(define (cons? c k)
  ;; xxx allocate?
  (closure-apply k (mpair? c)))
(define (cons-first c k)
  (closure-apply k (mcar c)))
(define (cons-rest c k)
  (closure-apply k (mcdr c)))
(define (cons-allocate f r k)
  (closure-apply k (mcons f r)))
(define (cons-set-first! c v k)
  (closure-apply k (set-mcar! c v)))
(define (cons-set-rest! c v k)
  (closure-apply k (set-mcdr! c v)))

(define (box? b k)
  ;; xxx allocate?
  (closure-apply k (racket:box? b)))
(define (box-deref b k)
  (closure-apply k (unbox b)))
(define (box-allocate v k)
  (closure-apply k (box v)))
(define (box-set! b v k)
  (closure-apply k (set-box! b v)))

;; xxx test first with gvector
;; xxx add parameterize interface to GC

(module+ test
  (require rackunit/chk)

  (define-syntax-rule (check-mutator . e)
    (mutator . e))

  (check-mutator 1)
  (check-mutator #t)
  (check-mutator #f)
  (check-mutator empty)
  (check-mutator '1)
  (check-mutator '#t)
  (check-mutator '#f)
  (check-mutator '())
  (check-mutator '(1 2))
  (check-mutator (λ (x) x))
  (check-mutator (λ (x y) (+ x y)))
  (check-mutator (let ([x 1]) x))
  (check-mutator (let* ([x 1] [y x]) y))
  (check-mutator (begin))
  (check-mutator (begin 1))
  (check-mutator (begin 1 2))
  (check-mutator (let ([x (box 1)]) (set-box! x 2) (unbox x)))
  (check-mutator (letrec ([x 1]) x))
  (check-mutator (empty? '()))
  (check-mutator (empty? 1))
  (check-mutator (if #t 1 2))
  (check-mutator (if #f 1 2))
  (check-mutator (letrec ([len
                           (λ (l)
                             (if (empty? l)
                               0
                               (+ 1 (len (rest l)))))])
                   (len '(1 2 3))))
  (check-mutator (define (len l)
                   (if (empty? l)
                     0
                     (+ 1 (len (rest l)))))
                 (len '(1 2 3)))
  (check-mutator (define x 1)
                 x)
  (check-mutator (define x 1)
                 x
                 (define y 2)
                 (+ x y))
  (check-mutator (+ 1 2))
  (check-mutator (- 1 2))
  (check-mutator (* 1 2))
  (check-mutator (/ 1 2))
  (check-mutator (sub1 2))
  (check-mutator (add1 2))
  (check-mutator (and))
  (check-mutator (and #t))
  (check-mutator (and 1))
  (check-mutator (and 1 2))
  (check-mutator (or))
  (check-mutator (or #t))
  (check-mutator (or 1))
  (check-mutator (or #f 1))
  (check-mutator (or #f 1 2))
  (check-mutator (or 1 2))
  (check-mutator (or #f 2))
  (check-mutator (cond))
  (check-mutator (cond [else 1]))
  (check-mutator (cond [#f 2] [else 1]))
  (check-mutator (cond [2 1] [else 1]))
  (check-mutator "string")
  (check-mutator (string=? "string" "string"))
  (check-mutator (string=? "string" "stringx"))
  (check-mutator 'symbol)
  (check-mutator (symbol=? 'symbol 'symbol))
  (check-mutator (symbol=? 'symbol 'symbolx))
  (check-mutator (= 1 2))
  (check-mutator (= 1 1))
  (check-mutator (equal? 1 1))
  (check-mutator (equal? 1 2))
  (check-mutator (equal? '(1 2) '(1)))
  (check-mutator (equal? '(1 2) '(1 2)))
  (check-mutator (printf "Hey there, ~a\n" "Jay"))
  (chk #:exn (check-mutator (error 'test "Hey there, ~a\n" "Jay")) "Jay")
  (chk #:exn
       (check-mutator (define x (cons 1 2))
                      (eq? x x))
       "contract violation")
  (check-mutator (not #t))
  (check-mutator (not #f))
  (check-mutator (when #t 1))
  (check-mutator (when #f 1))
  (check-mutator (unless #t 1))
  (check-mutator (unless #f 1))
  (check-mutator (test (+ 1 2) 3))
  (chk #:exn (check-mutator (test (+ 1 2) 4)) "not equal"))
