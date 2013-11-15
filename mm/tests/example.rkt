#lang racket/base
(require racket/bool
         racket/list
         data/gvector
         mm)

(define infinite-heap-collector@
  (collector
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
  (require (for-syntax racket/base)
           rackunit/chk)

  (define-syntax (chkm stx)
    (syntax-case stx ()
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
        '())
  (chkm (mutator '1)
        1)
  (chkm (mutator '#t)
        #t)
  (chkm (mutator '#f)
        #f)
  (chkm (mutator '())
        '())
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