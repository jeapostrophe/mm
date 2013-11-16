#lang racket/base
(require racket/match
         mm)

(define (stop-and-copy@ heap-size)
  (collector
   (define heap-ptr 0)
   (define FROM (make-heap heap-size))
   (define TO (make-heap heap-size))

   (define-syntax-rule (swap! x y)
     (let ([tmp y])
       (set! y x)
       (set! x tmp)))

   (define (stop-and-copy k v)
     (swap! FROM TO)
     (set! heap-ptr 0)
     (copy k v)
     (for ([i (in-range heap-size)])
       (FROM i FREE)))
   (define (copy k v)
     (copy-stack k)
     (copy-vector v))
   (define (copy-stack k)
     (unless (stack-bot? k)
       (copy-vector (stack-frame-env-addrs k))
       (copy-stack (stack-frame-parent k))))
   (define (copy-vector v)
     (for ([i (in-naturals)]
           [a (in-vector v)])
       (vector-set! v i (copy-addr a))))
   (define (copy-addr a)
     (define there heap-ptr)
     (match (FROM a)
       [(? number? new-a)
        new-a]
       ['atomic        
        (set! heap-ptr (+ heap-ptr 2))
        (FROM a there)
        (TO there 'atomic (FROM (+ a 1)))
        there]
       ['box
        (set! heap-ptr (+ heap-ptr 2))
        (FROM a there)
        (TO there 'box 'not-copied-yet)
        (TO (+ there 1) (copy-addr (FROM (+ a 1))))
        there]
       ['cons
        (set! heap-ptr (+ heap-ptr 3))
        (FROM a there)
        (TO there 'cons 
            'not-copied-yet
            'not-copied-yet)
        (TO (+ there 1) (copy-addr (FROM (+ a 1))))
        (TO (+ there 2) (copy-addr (FROM (+ a 2))))
        there]
       ['closure
        (define how-many (FROM (+ a 2)))
        (set! heap-ptr (+ heap-ptr 3 how-many))
        (FROM a there)
        (TO there 'closure
            (FROM (+ a 1))
            how-many)
        (for ([i (in-range how-many)])
          (TO (+ there 3 i) 'not-copied-yet))
        (for ([i (in-range how-many)])
          (TO (+ there 3 i)
              (copy-addr (FROM (+ a 3 i)))))
        there]
       [tag
        (error 'copy-addr "Unknown tag ~e @ ~a in: ~a" tag a FROM)]))

   (define (heap-allocate req k v)
     (or (heap-allocate-or-fail req)
         (and (stop-and-copy k v)
              (or (heap-allocate-or-fail req)
                  (error 'heap-allocate "Heap is too full for ~a: ~a" req TO)))))
   (define (heap-allocate-or-fail req)
     (define new-ptr (+ heap-ptr req))
     (if (> new-ptr heap-size)
       #f
       (begin0 heap-ptr
               (set! heap-ptr new-ptr))))

   (define (closure-allocate k f fvs)
     (define how-many (vector-length fvs))
     (define a (heap-allocate (+ 3 how-many) k fvs))
     (TO (+ a 0) 'closure f how-many)
     (for ([i (in-naturals)]
           [fv (in-vector fvs)])
       (TO (+ a 3 i) fv))
     (return k a))
   (define (closure? a)
     (eq? 'closure (TO a)))
   (define (closure-code-ptr a)
     (TO (+ a 1)))
   (define (closure-env-ref a i)
     (TO (+ a 3 i)))

   (define (atomic-allocate k x)
     (define a (heap-allocate 2 k (vector)))
     (TO (+ a 0) 'atomic x)
     (return k a))
   (define (atomic? a)
     (eq? 'atomic (TO (+ a 0))))
   (define (atomic-deref a)
     (TO (+ a 1)))

   (define (cons-allocate k f r)
     (define frv (vector f r))
     (define a (heap-allocate 3 k frv))
     (TO (+ a 0) 'cons (vector-ref frv 0) (vector-ref frv 1))
     (return k a))
   (define (cons? a)
     (eq? 'cons (TO (+ a 0))))
   (define (cons-first a)
     (TO (+ a 1)))
   (define (cons-rest a)
     (TO (+ a 2)))
   (define (cons-set-first! a nf)
     (TO (+ a 1) nf))
   (define (cons-set-rest! a nf)
     (TO (+ a 2) nf))

   (define (box-allocate k b)
     (define bv (vector b))
     (define a (heap-allocate 2 k bv))
     (TO (+ a 0) 'box (vector-ref bv 0))
     (return k a))
   (define (box? a)
     (eq? 'box (TO (+ a 0))))
   (define (box-deref a)
     (TO (+ a 1)))
   (define (box-set! a nb)
     (TO (+ a 1) nb))))

(module+ test
  (require rackunit/chk
           racket/list)

  (chk (mutator-run
        (stop-and-copy@ 6)
        (mutator 1 2 3))
       3)
  (chk (mutator-run
        (stop-and-copy@ 7)
        (mutator 1 2 3 (cons 4 5)))
       (cons 4 5))
  (chk (mutator-run
        (stop-and-copy@ 10)
        (mutator 1 2 3 (cons 4 5) 6))
       6)
  (chk (mutator-run
        (stop-and-copy@ 12)
        (mutator 1 2 3 (cons (cons 4 5) 6)))
       (cons (cons 4 5) 6))
  (chk (mutator-run
        (stop-and-copy@ 7)
        (mutator (box 1) 2))
       2)
  (chk (mutator-run
        (stop-and-copy@ 9)
        (mutator (cons (box 1) 2)))
       (cons (box 1) 2))
  (chk (mutator-run
        (stop-and-copy@ 15)
        (mutator (define x (cons 1 2))
                 (set-rest! x x)
                 3 4
                 (first x)))
       1)
  (chk (mutator-run
        (stop-and-copy@ 60)
        (mutator (define (len l)
                   (if (empty? l)
                     0
                     (add1 (len (rest l)))))
                 (define (sum l)
                   (if (empty? l)
                     0
                     (+ (first l)
                        (sum (rest l)))))

                 (define x
                   '(1 2 3 4 5))
                 (+ (len x)
                    (sum x))))
       (+ 5 (+ 1 2 3 4 5)))
  (visualize/stepper
   (chk (mutator-run
         (stop-and-copy@ 30)
         (mutator (define (my-even? x)
                    (if (zero? x)
                      #t
                      (my-odd? (sub1 x))))
                  (define (my-odd? x)
                    (if (zero? x)
                      #f
                      (my-even? (sub1 x))))
                  (my-even? 14)))
        #t)))
