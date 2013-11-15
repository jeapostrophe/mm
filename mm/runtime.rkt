#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax)
         racket/dict
         racket/syntax
         racket/list
         racket/match
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

(begin-for-syntax
  (require racket/unit-exptime))
(define-syntax (collector stx)
  (syntax-case stx ()
    [(_ e ...)
     (with-syntax
         ([([i-export e-export] ...)
           (let-values ([(_1 ids _2 _3) (signature-members #'collector^ stx)])
             (for/list ([i (in-list ids)])
               (list i (datum->syntax stx (syntax->datum i)))))])
       (syntax/loc stx
         (unit (import) (export collector^)
               e ...
               (define i-export e-export)
               ...)))]))

;; xxx contracts
(provide collector
         return
         mutator-run
         code-ptr?
         stack-bot?
         stack-frame? stack-frame-env-addrs stack-frame-parent)
