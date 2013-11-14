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

  (define-syntax-class mutator-keyword
    (pattern (~or (~literal if)
                  (~literal Mr.Gorbachev-unbox-these-identifiers!)
                  p:mutator-primitive p:mutator-lifted-primitive
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
     #:do [(pretty-print `(raw: ,(syntax->datum #'p)))]
     #:with ((~var m (mutator-program empty-id-table))) #'p
     #:do [(pretty-print `(mutator: ,(syntax->datum #'m.stx)))]
     (syntax/loc stx
       m.stx)]))

(struct mutator-atomic (value))
(struct mutator-lifted-primitive (prim args))
(struct mutator-primitive (prim-id args))
(struct mutator-lambda (params body))
(struct mutator-id (id))
(struct mutator-apply (fun args))
(struct mutator-if (test then else))

(require racket/unit)
(define-signature collector^
  (closure-apply
   mutator-equal? address=?
   ;;
   initialize
   closure-allocate
   box? box-allocate box-deref box-set!
   atomic-allocate atomic-deref
   cons? cons-allocate cons-first cons-rest cons-set-first! cons-set-rest!))

(require racket/match)
(define racket-collector@
  (unit
   (import) (export collector^)

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
     (match c
       [(? clo?)
        (apply
         (apply (clo-code-ptr c)
                (clo-free-vars c))
         args)]
       [#f
        (first args)]))

   (define (initialize)
     (void))

   ;; xxx make a separate "stack allocate" function for clarity?
   (define (closure-allocate f fvs k)
     (closure-apply k (clo f fvs)))

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
     (closure-apply k (set-box! b v)))))

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
                 (define id (contract ctc in:id 'pos 'neg))))]))
        (define-syntax-rule (defc* [id ctc] ...)
          (begin (defc id ctc) ...))

        (defc*
          [closure-apply
           (-> any/c
               any)]
          [mutator-equal?
           (-> heap-addr? heap-addr? cont?
               any)]
          [address=?
           (-> heap-addr? heap-addr? cont?
               any)]
          [initialize
           (-> any)]
          [closure-allocate
           (-> procedure? (listof heap-addr?) cont?
               any)]
          [box?
           (-> heap-addr? cont?
               any)]
          [box-allocate
           (-> heap-addr? cont?
               any)]
          [box-deref
           (-> heap-addr? cont?
               any)]
          [box-set!
           (-> heap-addr? heap-addr? cont?
               any)]
          [atomic-allocate
           (-> heap-value? cont?
               any)]
          [atomic-deref
           (-> heap-addr? cont?
               any)]
          [cons?
           (-> heap-addr? cont?
               any)]
          [cons-allocate
           (-> heap-addr? heap-addr? cont?
               any)]
          [cons-first
           (-> heap-addr? cont?
               any)]
          [cons-rest
           (-> heap-addr? cont?
               any)]
          [cons-set-first!
           (-> heap-addr? heap-addr? cont?
               any)]
          [cons-set-rest!
           (-> heap-addr? heap-addr? cont?
               any)])))

(define (mutator-run collector@ me)
  (define-values/invoke-unit
    (compound-unit
     (import) (export CTC)
     (link [([C : collector^]) collector@]
           [([CTC : collector^]) contract-collector@ C]))
    (import) (export collector^))

  (define (snoc l x)
    (append l (list x)))
  
  (define (interp env me k)
    (match me
      [(mutator-atomic v)
       (atomic-allocate v k)]
      [(mutator-id id)
       ;; xxx add good error message
       (closure-apply k (dict-ref env id))]
      [(mutator-lambda ids body)
       ;; xxx look through body for free-ids
       (closure-allocate
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
          addr)
        k)]
      [(mutator-primitive prim-name arg-mes)
       ;; xxx sequentialize this with continuation/closures
       (apply
        (match prim-name
          ['cons-allocate cons-allocate]
          ['cons-rest cons-rest]
          ['cons-first cons-first]
          ['cons-set-rest! cons-set-rest!]
          ['cons-set-first! cons-set-first!]
          ['box-allocate box-allocate]
          ['box-set! box-set!]
          ['box-deref box-deref]
          ['address=? address=?]
          ['mutator-equal? mutator-equal?]
          [_
           (error 'interp "Unknown primitive: ~e" prim-name)])
        (snoc (map (λ (me) (interp env me k)) arg-mes)
              k))]
      [(mutator-lifted-primitive prim arg-mes)
       ;; xxx sequentialize this with continuation/closures
       (interp
        env
        (mutator-atomic
         (apply
          prim
          (map (λ (addr) (atomic-deref addr k))
               (map (λ (me) (interp env me k)) arg-mes))))
        k)]
      [(mutator-apply fun-me arg-mes)
       ;; xxx sequentialize this with continuation/closures
       (closure-apply (interp env fun-me k)
                      (map (λ (me) (interp env me k)) arg-mes)
                      k)]
      [(mutator-if test true false)
       ;; xxx sequentialize this with continuation/closures
       (if (interp env test k)
         (interp env true k)
         (interp env false k))]))

  (local-require syntax/id-table
                 racket/dict)
  (define empty-env
    (make-immutable-free-id-table empty))

  (interp empty-env me #f))

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
        (mcons 1 (mcons 2 empty)))
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
