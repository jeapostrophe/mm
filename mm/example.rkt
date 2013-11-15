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
            [set-box! box-set!]
            [cons? cons?]
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

  (define mutator-cps-primitives
    (id-set [box box-allocate]
            [cons cons-allocate]))
  (define-syntax-class mutator-cps-primitive
    #:commit
    #:attributes (rewrite)
    (pattern x:id
             #:do [(define r (dict-ref mutator-cps-primitives #'x #f))]
             #:when r
             #:attr rewrite r))

  (define-syntax-class mutator-keyword
    (pattern (~or (~literal if)
                  (~literal Mr.Gorbachev-unbox-these-identifiers!)
                  p:mutator-primitive p:mutator-lifted-primitive
                  p:mutator-cps-primitive
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
    (pattern (prim:mutator-lifted-primitive (~var arg (mutator-expr ubs)) ...)
             #:attr stx
             (syntax/loc this-syntax
               (mutator-lifted-primitive prim (list arg.stx ...))))
    (pattern (prim:mutator-primitive (~var arg (mutator-expr ubs)) ...)
             #:attr stx
             (syntax/loc this-syntax
               (mutator-primitive 'prim.rewrite (list arg.stx ...))))
    (pattern (prim:mutator-cps-primitive (~var arg (mutator-expr ubs)) ...)
             #:attr stx
             (syntax/loc this-syntax
               (mutator-cps-primitive 'prim.rewrite (list arg.stx ...))))
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
    (pattern (~seq e p ...+)
             #:with (~var b (mutator-expr ubs))
             (syntax/loc #'e
               (let ([ignored e]) p ...))
             #:attr stx #'b.stx)
    (pattern (~seq e)
             #:with (~var b (mutator-expr ubs)) #'e
             #:attr stx #'b.stx)))

(begin-for-syntax
  (require racket/pretty))
(define-syntax (mutator stx)
  (syntax-parse stx
    [(_ . p)
     ;;#:do [(pretty-print `(raw: ,(syntax->datum #'p)))]
     #:with ((~var m (mutator-program empty-id-table))) #'p
     ;;#:do [(pretty-print `(mutator: ,(syntax->datum #'m.stx)))]
     (syntax/loc stx
       m.stx)]))

(struct mutator-atomic (value) #:transparent)
(struct mutator-primitive (prim-id args) #:transparent)
(struct mutator-lifted-primitive (prim args) #:transparent)
(struct mutator-cps-primitive (prim-id args) #:transparent)
(struct mutator-lambda (params body) #:transparent)
(struct mutator-id (id) #:transparent)
(struct mutator-apply (fun args) #:transparent)
(struct mutator-apply1 (fun arg) #:transparent)
(struct mutator-if (test then else) #:transparent)

(struct closure-apply (k a))

(require racket/unit)
(define-signature collector^
  (mutator-equal?
   address=?
   ;;
   initialize
   closure? closure-allocate
   box? box-allocate box-deref box-set!
   atomic-allocate atomic-deref
   cons? cons-allocate cons-first cons-rest cons-set-first! cons-set-rest!))

(require racket/match
         data/gvector)
(define racket-collector@
  (unit
   (import) (export collector^)

   (define (address=? x y)
     (= x y))
   (define (mutator-equal? x y)
     ;; xxx really should walk these pointers
     (equal? x y))

   (define HEAP (make-gvector))

   ;; Uses
   (define (initialize)
     (void))

   ;; xxx make a separate "stack allocate" function for clarity?
   (define (closure? a)
     (eq? 'closure (gvector-ref HEAP a)))
   (define (closure-allocate k f fvs)
     (define a (gvector-count HEAP))
     (apply gvector-add! HEAP 'closure f fvs)
     (closure-apply k a))

   (define (atomic-allocate k x)
     (define a (gvector-count HEAP))
     (gvector-add! HEAP 'atomic x)
     (closure-apply k a))
   (define (atomic-deref a)
     (printf "ad: ~a ~v\n" a (gvector->list HEAP))
     (gvector-ref HEAP (+ a 1)))

   (define (cons-allocate k f r)
     (define a (gvector-count HEAP))
     (gvector-add! HEAP 'cons f r)
     (closure-apply k a))
   (define (cons? a)
     (eq? 'cons (gvector-ref HEAP (+ a 0))))
   (define (cons-first a)
     (gvector-ref HEAP (+ a 1)))
   (define (cons-rest a)
     (gvector-ref HEAP (+ a 2)))
   (define (cons-set-first! a nf)
     (gvector-set! HEAP (+ a 1) nf))
   (define (cons-set-rest! a nf)
     (gvector-set! HEAP (+ a 2) nf))

   (define (box-allocate k b)
     (define a (gvector-count HEAP))
     (gvector-add! HEAP 'box b)
     (closure-apply k a))
   (define (box? a)
     (eq? 'box (gvector-ref HEAP (+ a 0))))
   (define (box-deref a)
     (gvector-ref HEAP (+ a 1)))
   (define (box-set! a nb)
     (gvector-set! HEAP (+ a 1) nb))))

(require racket/contract)
(define heap-value?
  (or/c exact-integer? boolean? empty? void? string? symbol?))
(define heap-addr?
  exact-nonnegative-integer?)
(define cont?
  (or/c heap-addr? #f))

(define contract-collector@
  (unit (import (prefix in: collector^))
        (export collector^)

        (define-syntax (defc stx)
          (syntax-parse stx
            [(_ id ctc)
             (with-syntax ([in:id (format-id #'id "in:~a" #'id)])
               (syntax/loc stx
                 (define id (contract ctc in:id 'collector 'mutator-internals))))]))
        (define-syntax-rule (defc* [id ctc] ...)
          (begin (defc id ctc) ...))

        (defc*
          [mutator-equal?
           (-> heap-addr? heap-addr?
               boolean?)]
          [address=?
           (-> heap-addr? heap-addr?
               boolean?)]
          [initialize
           (-> any)]
          [closure?
           (-> heap-addr?
               boolean?)]
          [closure-allocate
           (-> cont? procedure? (listof heap-addr?)
               any)]
          [box?
           (-> heap-addr?
               boolean?)]
          [box-allocate
           (-> cont? heap-addr?
               any)]
          [box-deref
           (-> heap-addr?
               heap-addr?)]
          [box-set!
           (-> heap-addr? heap-addr?
               void?)]
          [atomic-allocate
           (-> cont? heap-value?
               any)]
          [atomic-deref
           (-> heap-addr?
               heap-value?)]
          [cons?
           (-> heap-addr?
               boolean?)]
          [cons-allocate
           (-> cont? heap-addr? heap-addr?
               any)]
          [cons-first
           (-> heap-addr?
               heap-addr?)]
          [cons-rest
           (-> heap-addr?
               heap-addr?)]
          [cons-set-first!
           (-> heap-addr? heap-addr?
               void?)]
          [cons-set-rest!
           (-> heap-addr? heap-addr?
               void?)])))

(define (mutator-run collector@ me)
  (let/ec esc
    (define-values/invoke-unit
      (compound-unit
       (import) (export CTC)
       (link [([C : collector^]) collector@]
             [([CTC : collector^]) contract-collector@ C]))
      (import) (export collector^))

    (define (wrap-in-apply arg-mes inside)
      (define-values (arg-ids args-with-ids new-args)
        (for/fold ([arg-ids empty]
                   [args-with-ids empty]
                   [new-args empty])
            ([arg (in-list arg-mes)])
          (cond
            [(mutator-id? arg)
             (values arg-ids
                     args-with-ids
                     (cons arg new-args))]
            [else
             (define new-id (generate-temporary arg))
             (values (cons new-id arg-ids)
                     (cons arg args-with-ids)
                     (cons (mutator-id new-id) new-args))])))
      (for/fold ([me (inside (reverse new-args))])
          ([ai (in-list arg-ids)]
           [ae (in-list args-with-ids)])
        (mutator-apply1 (mutator-lambda (list ai) me) ae)))

    (define (atomic-deref* id a)
      (printf "atomic-deref* ~a ~a\n" id a)
      (define v (atomic-deref a))
      v)

    (define (->racket a)
      (cond
        [(cons? a)
         (cons (->racket (cons-first a))
               (->racket (cons-rest a)))]
        [(box? a)
         (box (->racket (box-deref a)))]
        [(closure? a)
         (λ (x) x)]
        [else
         (atomic-deref a)]))

    (eprintf "start\n")
    (define (interp env me k)
      (eprintf "interp ~v ~v\n" me k)
      (define (lookup i)
        (dict-ref env i
                  (λ ()
                    (error 'mutator "Unbound identifier: ~e" i))))
      (define trampoline
        (match me
          [(mutator-atomic v)
           (atomic-allocate k v)]
          [(mutator-id id)
           (closure-apply k (lookup id))]
          [(mutator-apply1 (mutator-lambda (list id) body) arg-me)
           
           (closure-allocate 
            ...
            (λ free-vs
              (λ (lam-addr dyn-k)
                ...))
            ... vars mentioned in body ...)

           (interp env arg-me k)

           (error 'xxx)]
          [(mutator-lambda ids body)
           ;; xxx look through body for free-ids
           (closure-allocate
            k
            (λ free-vs
              (define free-env
                (for/fold ([free-env empty-env])
                    ([(k old-addr) (in-dict env)]
                     [new-addr (in-list free-vs)])
                  (dict-set free-env k new-addr)))
              (λ (vs dyn-k)
                (define new-env
                  (for/fold ([new-env free-env])
                      ([i (in-list ids)]
                       [v (in-list vs)])
                    (dict-set new-env i v)))
                (interp new-env body dyn-k)))
            (for/list ([(k addr) (in-dict env)])
              addr))]
          [(mutator-primitive prim-name (and arg-mes (list (? mutator-id?) ...)))
           (closure-apply
            k
            (apply
             (match prim-name
               ['cons-rest cons-rest]
               ['cons-first cons-first]
               ['cons-set-rest! cons-set-rest!]
               ['cons-set-first! cons-set-first!]
               ['box-set! box-set!]
               ['box-deref box-deref]
               ['address=? address=?]
               ['mutator-equal? mutator-equal?]
               [_
                (error 'interp "Unknown primitive: ~e" prim-name)])
             (map lookup arg-mes)))]
          [(mutator-primitive prim-name arg-mes)
           (interp env
                   (wrap-in-apply
                    arg-mes
                    (λ (new-args)
                      (mutator-primitive prim-name new-args)))
                   k)]
          [(mutator-cps-primitive prim-name (and arg-mes (list (? mutator-id?) ...)))
           (apply
            (match prim-name
              ['cons-allocate cons-allocate]
              [_
               (error 'interp "Unknown CPS primitive: ~e" prim-name)])
            k
            (map lookup arg-mes))]
          [(mutator-cps-primitive prim-name arg-mes)
           (interp env
                   (wrap-in-apply
                    arg-mes
                    (λ (new-args)
                      (mutator-cps-primitive prim-name new-args)))
                   k)]
          [(mutator-lifted-primitive prim (and arg-mes (list (? mutator-id?) ...)))
           (interp
            env
            (mutator-atomic
             (apply
              prim
              (map (compose (curry atomic-deref* 'lifted-prim) lookup) arg-mes)))
            k)]
          [(mutator-lifted-primitive prim arg-mes)
           (interp env
                   (wrap-in-apply
                    arg-mes
                    (λ (new-args)
                      (mutator-lifted-primitive prim new-args)))
                   k)]
          [(mutator-if (mutator-id test-id) true false)
           (if (atomic-deref* 'if (lookup test-id))
             (interp env true k)
             (interp env false k))]
          [(mutator-if test true false)
           (define test-id (generate-temporary test))
           (interp
            env
            (wrap-in-apply
             (list test)
             (λ (new-ids)
               (mutator-if (first new-ids) true false)))
            k)]
          [(mutator-apply (? mutator-id? fun-me) (list (? mutator-id? arg-mes) ...))
           (closure-apply (lookup fun-me)
                          (map lookup arg-mes)
                          k)]
          [(mutator-apply fun-me (list arg-mes ...))
           (interp env
                   (wrap-in-apply
                    (cons fun-me arg-mes)
                    (λ (new-ids)
                      (mutator-apply (first new-ids)
                                     (rest new-ids))))
                   k)]))
      (match-define (closure-apply ck ca) trampoline)
      (match ck
        [#f
         (esc (->racket ca))]
        [_
         (error 'xxx "~v" (vector ck ca))]))

    (local-require syntax/id-table
                   racket/function
                   racket/dict
                   racket/syntax)
    (define empty-env
      (make-immutable-free-id-table empty))

    (interp empty-env me #f)))

;; xxx test first with gvector
;; xxx add parameterize interface to GC
;; xxx optional functions

(module+ test
  (require rackunit/chk)

  (define-syntax (chkm stx)
    (syntax-parse stx
      [(_ e v)
       (quasisyntax/loc stx
         (chk #,(syntax/loc stx (mutator-run racket-collector@ e))
              v))]))

  (chkm (mutator 1)
        1)
  (chkm (mutator #t)
        #t)
  (chkm (mutator #f)
        #f)
  (chkm (mutator empty)
        empty)
  (chkm (mutator '1)
        1)
  (chkm (mutator '#t)
        #t)
  (chkm (mutator '#f)
        #f)
  (chkm (mutator '())
        empty)
  (chkm (mutator '(1 2))
        '(1 2))
  (chkm (mutator ((λ (x) x) 1))
        1)
  (chkm (mutator ((λ (x y) (+ x y)) 2 3))
        5)
  (chkm (mutator (let ([x 1]) x))
        1)
  (chkm (mutator (let* ([x 1] [y x]) y))
        1)
  (chkm (mutator (begin))
        (void))
  (chkm (mutator (begin 1))
        1)
  (chkm (mutator (begin 1 2))
        2)
  (chkm (mutator (let ([x (box 1)]) (set-box! x 2) (unbox x)))
        2)
  (chkm (mutator (letrec ([x 1]) x))
        1)
  (chkm (mutator (empty? '()))
        #t)
  (chkm (mutator (empty? 1))
        #f)
  (chkm (mutator (if #t 1 2))
        1)
  (chkm (mutator (if #f 1 2))
        2)
  (chkm (mutator (letrec ([len
                           (λ (l)
                             (if (empty? l)
                               0
                               (+ 1 (len (rest l)))))])
                   (len '(1 2 3))))
        3)
  (chkm (mutator (define (len l)
                   (if (empty? l)
                     0
                     (+ 1 (len (rest l)))))
                 (len '(1 2 3)))
        3)
  (chkm (mutator (define x 1)
                 x)
        1)
  (chkm (mutator (define x 1)
                 x
                 (define y 2)
                 (+ x y))
        3)
  (chkm (mutator (+ 1 2))
        3)
  (chkm (mutator (- 1 2))
        -1)
  (chkm (mutator (* 1 2))
        2)
  (chkm (mutator (/ 1 2))
        1/2)
  (chkm (mutator (sub1 2))
        1)
  (chkm (mutator (add1 2))
        3)
  (chkm (mutator (and))
        #t)
  (chkm (mutator (and #t))
        #t)
  (chkm (mutator (and 1))
        1)
  (chkm (mutator (and 1 2))
        2)
  (chkm (mutator (or))
        #f)
  (chkm (mutator (or #t))
        #t)
  (chkm (mutator (or 1))
        1)
  (chkm (mutator (or #f 1))
        1)
  (chkm (mutator (or #f 1 2))
        1)
  (chkm (mutator (or 1 2))
        1)
  (chkm (mutator (or #f 2))
        2)
  (chkm (mutator (cond))
        (void))
  (chkm (mutator (cond [else 1]))
        1)
  (chkm (mutator (cond [#f 2] [else 1]))
        1)
  (chkm (mutator (cond [2 1] [else 3]))
        1)
  (chkm (mutator "string")
        "string")
  (chkm (mutator (string=? "string" "string"))
        #t)
  (chkm (mutator (string=? "string" "stringx"))
        #f)
  (chkm (mutator 'symbol)
        'symbol)
  (chkm (mutator (symbol=? 'symbol 'symbol))
        #t)
  (chkm (mutator (symbol=? 'symbol 'symbolx))
        #f)
  (chkm (mutator (= 1 2))
        #f)
  (chkm (mutator (= 1 1))
        #t)
  (chkm (mutator (equal? 1 1))
        #t)
  (chkm (mutator (equal? 1 2))
        #f)
  (chkm (mutator (equal? '(1 2) '(1)))
        #f)
  (chkm (mutator (equal? '(1 2) '(1 2)))
        #t)
  (chkm (mutator (printf "Hey there, ~a\n" "Jay"))
        (void))
  (chk #:exn
       (mutator-run racket-collector@
                    (mutator (error 'test "Hey there, ~a\n" "Jay")))
       "Jay")
  (chk #:exn
       (mutator-run racket-collector@
                    (mutator (define x (cons 1 2))
                             (eq? x x)))
       "contract violation")
  (chkm (mutator (not #t))
        #f)
  (chkm (mutator (not #f))
        #t)
  (chkm (mutator (when #t 1))
        1)
  (chkm (mutator (when #f 1))
        (void))
  (chkm (mutator (unless #t 1))
        (void))
  (chkm (mutator (unless #f 1))
        1)
  (chkm (mutator (test (+ 1 2) 3))
        (void))
  (chk #:exn
       (mutator-run racket-collector@
                    (mutator (test (+ 1 2) 4)))
       "not equal"))
