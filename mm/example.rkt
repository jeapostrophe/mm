#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/list
                     racket/syntax)
         racket/stxparam
         racket/list)

;; Mutator Source Language (Scheme-like) compiler to use allocator
(begin-for-syntax
  (require syntax/id-table
           racket/dict)
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
         (begin (set-box! b (unbox-these (b ...) be))
                ...
                (unbox-these (b ...) 
                             (let () . bb)))))]))

(define-syntax (unbox-these stx)
  (raise-syntax-error 'unbox-these "Illegal outside mutator" stx))

(begin-for-syntax
  (define-syntax-class mutator-lifted-primitive
    #:commit
    (pattern (~literal +))
    (pattern (~literal -))
    (pattern (~literal *))
    (pattern (~literal /))
    (pattern (~literal add1))
    (pattern (~literal sub1))
    (pattern (~literal empty?)))

  (define-syntax-class mutator-primitive
    #:commit
    #:attributes (rewrite)
    (pattern (~literal unbox)
             #:attr rewrite #'box-deref)
    (pattern (~literal box)
             #:attr rewrite #'box-allocate)
    (pattern (~literal set-box!)
             #:attr rewrite #'box-set!)
    (pattern (~literal cons)
             #:attr rewrite #'cons-allocate)
    (pattern (~literal first)
             #:attr rewrite #'cons-first)
    (pattern (~literal rest)
             #:attr rewrite #'cons-rest))

  (define-syntax-class (mutator-expr ubs)
    #:commit
    #:attributes (stx)
    (pattern ((~literal unbox-these) (x:id ...) e)
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
    (pattern ((~literal set!) x:id
              (~var arg (mutator-expr ubs)))
             #:attr stx
             (syntax/loc this-syntax
               (set! x arg.stx)))
    (pattern (prim:mutator-lifted-primitive
              (~var arg (mutator-expr ubs)) ...)
             #:attr stx
             (syntax/loc this-syntax
               (prim (atomic-deref arg.stx) ...)))
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
    (pattern n:number
             #:attr stx
             (syntax/loc this-syntax
               (atomic-allocate n)))
    (pattern b:boolean
             #:attr stx
             (syntax/loc this-syntax
               (atomic-allocate b)))
    (pattern (m:mutator-macro . body)
             #:with (~var e (mutator-expr ubs)) ((attribute m.expander) this-syntax)
             #:attr stx #'e.stx)
    (pattern ((~and (~not (~or (~literal if) (~literal set!)
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
    (pattern n:number
             #:attr ids empty)
    (pattern b:boolean
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
    (pattern ((~literal set!) x:id v:cps-atom)
             #:attr stx
             (quasisyntax/loc this-syntax
               (#,k (set! x v))))
    (pattern ((~literal set!) x:id e)
             #:with e-k (generate-temporary 'set!-k)
             #:with (~var cps-e (cps-expr #'e-k)) #'e
             #:with e-id (generate-temporary 'set!-id)
             #:with (~var cps-b (cps-expr k)) #'(set! x e-id)
             #:attr stx
             (syntax/loc this-syntax
               ((λ (e-k) cps-e.stx)
                (λ (e-id) cps-b.stx))))
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
             #:with (~var cps-b (cps-expr k)) #'(before ... middle-id after ...)
             #:attr stx
             (syntax/loc this-syntax
               ((λ (middle-k) cps-middle.stx)
                (λ (middle-id) cps-b.stx))))))

;; Lambda lifting and closure conversion for cps output
(begin-for-syntax
  (define (list->id-set ks)
    (make-immutable-free-id-table
     (for/list ([k (in-list ks)])
       (cons k #t))))
  (define (id-set-union ids-l)
    (for*/fold ([all-ids (make-immutable-free-id-table empty)])
        ([next-ids (in-list ids-l)]
         [next-id (in-dict-keys next-ids)])
      (dict-set all-ids next-id #t)))
  (define (id-set->list ids)
    (for/list ([k (in-dict-keys ids)])
      k))
  (define (id-set-remove ids lst)
    (for/fold ([ids ids]) ([k (in-list (syntax->list lst))])
      (dict-remove ids k)))

  ;; xxx merge with primitives so I don't need to write it twice
  (define lift-globals
    #'(stack-exit
       box-set! box-allocate box-deref
       cons-first cons-rest cons-allocate
       atomic-allocate atomic-deref
       add1 sub1 empty?
       empty void
       + * / -))

  (define-syntax-class lift-expr
    #:attributes (stx lambdas ids)
    (pattern ((~literal λ) (x:id ...) body:lift-expr)
             #:with λ-id (generate-temporary 'λ-id)
             #:attr ids (id-set-remove (attribute body.ids) #'(λ-id x ...))
             #:with (fv ...) (id-set->list (attribute ids))
             #:attr lambdas
             #'([λ-id (λ (fv ...) (λ (x ...) body.stx))]
                . body.lambdas)
             #:attr stx
             (syntax/loc this-syntax
               (closure-allocate λ-id fv ...)))
    (pattern ((~literal set!) x:id a:cps-atom)
             #:attr ids
             (id-set-remove
              (list->id-set (cons #'x (attribute a.ids)))
              lift-globals)
             #:attr lambdas #'()
             #:attr stx this-syntax)
    (pattern ((~literal if) ca:cps-atom t:lift-expr f:lift-expr)
             #:attr ids
             (id-set-union (list
                            (id-set-remove
                             (list->id-set (attribute ca.ids))
                             lift-globals)
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
              lift-globals)
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
     #:with ((~var m (mutator-program (make-immutable-free-id-table empty)))) #'p
     #:with (~var c (cps-expr #'stack-exit)) #'m.stx
     #:with l:lift-expr #'c.stx
     #:with l-output #'(lifted l.lambdas l.stx)
     (syntax/loc stx
       (begin
         ;; (pretty-print '(raw: p))
         ;; (pretty-print '(mutator: m.stx))
         ;; (pretty-print '(cps: c.stx))
         ;; (pretty-print '(lift: l-output))
         l-output))]))

(define-syntax-rule
  (lifted ([lam lam-body] ...)
          body)
  (letrec ([lam lam-body] ...)
    body))

;; Uses
(struct clo (code-ptr free-vars) #:transparent)

(define (closure-apply c . args)
  (if (clo? c)
    (apply
     (apply (clo-code-ptr c)
            (clo-free-vars c))
     args)
    (apply c args)))

(define (stack-exit v) 
  v)
(define (closure-allocate f . fvs)
  (clo f fvs))
(define (atomic-allocate x k)
  (closure-apply k x))
(define (atomic-deref x k)
  (closure-apply k x))
(define (cons-first c k)
  (closure-apply k (first c)))
(define (cons-rest c k)
  (closure-apply k (rest c)))
(define (cons-allocate f r k)
  (closure-apply k (cons f r)))
(define (box-deref b k)
  (closure-apply k (unbox b)))
(define (box-allocate v k)
  (closure-apply k (box v)))
(define (box-set! b v k) 
  (closure-apply k (set-box! b v)))

;; xxx add cons? box? atomic? set-first! set-rest!
;; xxx add parameterize interface to GC

(module+ test
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
  (check-mutator (let ([x 1]) (set! x 2) x))
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
  (check-mutator (add1 2)))
