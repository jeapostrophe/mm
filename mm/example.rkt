#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax)
         racket/function
         racket/dict
         racket/syntax
         racket/bool
         racket/list
         "id-table.rkt"
         "ast.rkt"
         "compiler.rkt")

(struct code-ptr (fv-count f))

(struct return (k a))
(struct stack ())
(struct stack-bot stack ())
(struct stack-frame stack (return-id return-body env-ids env-addrs parent))

(require racket/unit)
(define-signature collector^
  (initialize
   closure? closure-allocate closure-code-ptr closure-env-ref
   box? box-allocate box-deref box-set!
   atomic? atomic-allocate atomic-deref
   cons? cons-allocate cons-first cons-rest cons-set-first! cons-set-rest!))

(require racket/contract)
(define heap-value/c
  (or/c number? boolean? empty? void? string? symbol? code-ptr?))
(define heap-addr?
  exact-nonnegative-integer?)

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
          [initialize
           (-> any)]
          [closure-allocate
           (-> stack? code-ptr? (vectorof heap-addr?)
               return?)]
          [closure?
           (-> heap-addr?
               boolean?)]
          [closure-code-ptr
           (-> heap-addr?
               code-ptr?)]
          [closure-env-ref
           (-> heap-addr? exact-nonnegative-integer?
               heap-addr?)]
          [box-allocate
           (-> stack? heap-addr?
               return?)]
          [box?
           (-> heap-addr?
               boolean?)]
          [box-deref
           (-> heap-addr?
               heap-addr?)]
          [box-set!
           (-> heap-addr? heap-addr?
               void?)]
          [atomic-allocate
           (-> stack? heap-value/c
               return?)]
          [atomic?
           (-> heap-addr?
               boolean?)]
          [atomic-deref
           (-> heap-addr?
               heap-value/c)]
          [cons-allocate
           (-> stack? heap-addr? heap-addr?
               return?)]
          [cons?
           (-> heap-addr?
               boolean?)]
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

(define (address=? x y)
  (= x y))

(define (wrap-in-apply1 arg-mes inside)
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

(define (mutator-run collector@ me)
  (define-values/invoke-unit
    (compound-unit
     (import) (export CTC)
     (link [([C : collector^]) collector@]
           [([CTC : collector^]) contract-collector@ C]))
    (import) (export collector^))

  (define (mutator-equal? x y)
    (cond
      [(address=? x y)
       #t]
      [(and (cons? x) (cons? y))
       (and (mutator-equal? (cons-first x) (cons-first y))
            (mutator-equal? (cons-rest x) (cons-rest y)))]
      [(and (box? x) (box? y))
       (mutator-equal? (box-deref x) (box-deref y))]
      [(and (atomic? x) (atomic? y))
       (equal? (atomic-deref x) (atomic-deref y))]
      [else
       #f]))

  (define (->racket a)
    (cond
      [(cons? a)
       (cons (->racket (cons-first a))
             (->racket (cons-rest a)))]
      [(box? a)
       (box (->racket (box-deref a)))]
      [(closure? a)
       (error 'mutator "Cannot export closures to Racket")]
      [else
       (atomic-deref a)]))

  (define (env-set label env i v)
    (unless (heap-addr? v)
      (error 'env-set "~a: cannot set environment id ~a to non-heap-value: ~a\n"
             label i v))
    (dict-set env i v))

  (define (interp env me k)
    (define (lookup i)
      (dict-ref env i
                (λ ()
                  (error 'mutator "Unbound identifier: ~e" i))))
    (define (ids->addrs free-var-ids)
      (for/vector ([k (in-list free-var-ids)])
        (lookup k)))
    (match me
      [(mutator-atomic v)
       (atomic-allocate k v)]
      [(mutator-id id)
       (return k (lookup id))]
      [(mutator-apply1 (and fun-me (mutator-lambda (list id) body)) arg-me)
       (define free-var-ids (mutator-free-vars fun-me))
       (interp env arg-me
               (stack-frame
                id body
                free-var-ids
                (ids->addrs free-var-ids)
                k))]
      [(and fun-me (mutator-lambda ids body))
       (define free-var-ids (mutator-free-vars fun-me))
       (closure-allocate
        k
        (code-ptr
         (length free-var-ids)
         (λ (free-var-addrs)
           (define free-env
             (for/fold ([free-env empty-id-table])
                 ([k (in-list free-var-ids)]
                  [new-addr (in-list free-var-addrs)])
               (env-set 'clo-free free-env k new-addr)))
           (λ (vs dyn-k)
             (define new-env
               (for/fold ([new-env free-env])
                   ([i (in-list ids)]
                    [v (in-list vs)])
                 (env-set 'clo-new new-env i v)))
             (interp new-env body dyn-k))))
        (ids->addrs free-var-ids))]
      [(mutator-apply (mutator-id fun-id) (list (mutator-id arg-ids) ...))
       (define fun-addr (lookup fun-id))
       (match-define (code-ptr fv-count f) (closure-code-ptr fun-addr))
       (define fv-addrs
         (for/list ([i (in-range fv-count)])
           (closure-env-ref fun-addr i)))
       ((f fv-addrs) (map lookup arg-ids) k)]
      [(mutator-if (mutator-id test-id) true false)
       (if (atomic-deref (lookup test-id))
         (interp env true k)
         (interp env false k))]
      ;; Primitives
      [(mutator-primitive prim-name (list (mutator-id arg-ids) ...))
       (define-values (prim type)
         (match prim-name
           ['cons-rest (values cons-rest 'addr)]
           ['cons-first (values cons-first 'addr)]
           ['cons-set-rest! (values cons-set-rest! 'value)]
           ['cons-set-first! (values cons-set-first! 'value)]
           ['box-set! (values box-set! 'value)]
           ['box-deref (values box-deref 'addr)]
           ['address=? (values address=? 'value)]
           ['mutator-equal? (values mutator-equal? 'value)]
           ['cons-allocate (values cons-allocate 'cps)]
           ['box-allocate (values box-allocate 'cps)]
           [(? procedure?) (values prim-name 'external)]
           [_
            (error 'interp "Unknown primitive: ~e" prim-name)]))
       (define arg-addrs
         (map lookup arg-ids))
       (match type
         ['external
          (interp env (mutator-atomic (apply prim (map atomic-deref arg-addrs))) k)]
         ['cps
          (apply prim k arg-addrs)]
         ['value
          (interp env (mutator-atomic (apply prim arg-addrs)) k)]
         ['addr
          (return k (apply prim arg-addrs))])]
      ;; Sequencing
      [(mutator-primitive prim-name arg-mes)
       (interp env
               (wrap-in-apply1
                arg-mes
                (λ (new-args)
                  (mutator-primitive prim-name new-args)))
               k)]
      [(mutator-if test true false)
       (interp
        env
        (wrap-in-apply1
         (list test)
         (λ (new-ids)
           (mutator-if (first new-ids) true false)))
        k)]
      [(mutator-apply fun-me (list arg-mes ...))
       (interp env
               (wrap-in-apply1
                (cons fun-me arg-mes)
                (λ (new-ids)
                  (mutator-apply (first new-ids)
                                 (rest new-ids))))
               k)]))

  (let loop ([trampoline
              (interp empty-id-table me (stack-bot))])
    (match trampoline
      [(return (stack-bot) ca)
       (->racket ca)]
      [(return (stack-frame id body env-ids env-addrs k) ca)
       (loop
        (interp (env-set
                 'new-arg
                 (for/fold ([new-env empty-id-table])
                     ([i (in-list env-ids)]
                      [a (in-vector env-addrs)])
                   (env-set 'recover-env new-env i a))
                 id ca)
                body
                k))])))

;; xxx optional functions
;; xxx collector param over heap

(require racket/match
         data/gvector)
(define infinite-heap-collector@
  (unit
   (import) (export collector^)

   (define HEAP (make-gvector))
   (define (gvector->disp g)
     (for/list ([i (in-naturals)]
                [e (in-gvector g)])
       (cons i e)))

   ;; Uses
   (define (initialize)
     (void))

   (define (closure-allocate k f fvs)
     (define a (gvector-count HEAP))
     (gvector-add! HEAP 'closure f)
     (for ([fv (in-vector fvs)])
       (gvector-add! HEAP fv))
     (return k a))
   (define (closure? a)
     (eq? 'closure (gvector-ref HEAP a)))
   (define (closure-code-ptr a)
     (gvector-ref HEAP (+ a 1)))
   (define (closure-env-ref a i)
     (gvector-ref HEAP (+ a 2 i)))

   (define (atomic-allocate k x)
     (define a (gvector-count HEAP))
     (gvector-add! HEAP 'atomic x)
     (return k a))
   (define (atomic? a)
     (eq? 'atomic (gvector-ref HEAP (+ a 0))))
   (define (atomic-deref a)
     (gvector-ref HEAP (+ a 1)))

   (define (cons-allocate k f r)
     (define a (gvector-count HEAP))
     (gvector-add! HEAP 'cons f r)
     (return k a))
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
     (return k a))
   (define (box? a)
     (eq? 'box (gvector-ref HEAP (+ a 0))))
   (define (box-deref a)
     (gvector-ref HEAP (+ a 1)))
   (define (box-set! a nb)
     (gvector-set! HEAP (+ a 1) nb))))

(module+ test
  (require rackunit/chk)

  (define-syntax (chkm stx)
    (syntax-parse stx
      [(_ e v)
       (quasisyntax/loc stx
         (chk #,(syntax/loc stx (mutator-run infinite-heap-collector@ e))
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
       (mutator-run infinite-heap-collector@
                    (mutator (error 'test "Hey there, ~a\n" "Jay")))
       "Jay")
  (chkm (mutator (define x (cons 1 2))
                 (eq? x x))
        #t)
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
       (mutator-run infinite-heap-collector@
                    (mutator (test (+ 1 2) 4)))
       "not equal")
  (chkm (mutator (unbox (box 1)))
        1))
