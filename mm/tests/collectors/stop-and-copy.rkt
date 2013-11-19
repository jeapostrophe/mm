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
       (heap-set! FROM i FREE)))
   (define (copy k v)
     (copy-stack k)
     (copy-vector v))
   (define (copy-stack k)
     (unless (stack-bot? k)
       (copy-vector (stack-frame-locals k))
       (copy-stack (stack-frame-parent k))))
   (define (copy-vector v)
     (for ([i (in-naturals)]
           [a (in-vector v)])
       (vector-set! v i (copy-addr a))))
   (define (copy-addr a)
     (define there heap-ptr)
     (match (heap-ref FROM a)
       [(? number? new-a)
        new-a]
       ['atomic        
        (set! heap-ptr (+ heap-ptr 2))
        (heap-set! FROM a there)
        (heap-set! TO there 'atomic (heap-ref FROM (+ a 1)))
        there]
       ['box
        (set! heap-ptr (+ heap-ptr 2))
        (heap-set! FROM a there)
        (heap-set! TO there 'box 'not-copied-yet)
        (heap-set! TO (+ there 1) (copy-addr (heap-ref FROM (+ a 1))))
        there]
       ['cons
        (set! heap-ptr (+ heap-ptr 3))
        (heap-set! FROM a there)
        (heap-set! TO there 'cons 
            'not-copied-yet
            'not-copied-yet)
        (heap-set! TO (+ there 1) (copy-addr (heap-ref FROM (+ a 1))))
        (heap-set! TO (+ there 2) (copy-addr (heap-ref FROM (+ a 2))))
        there]
       ['closure
        (define how-many (heap-ref FROM (+ a 2)))
        (set! heap-ptr (+ heap-ptr 3 how-many))
        (heap-set! FROM a there)
        (heap-set! TO there 'closure
            (heap-ref FROM (+ a 1))
            how-many)
        (for ([i (in-range how-many)])
          (heap-set! TO (+ there 3 i) 'not-copied-yet))
        (for ([i (in-range how-many)])
          (heap-set! TO (+ there 3 i)
              (copy-addr (heap-ref FROM (+ a 3 i)))))
        there]
       [tag
        (error 'copy-addr "Unknown tag ~e @ ~a in: ~a" tag a FROM)]))

   (define (heap-allocate req k v)
     (or (heap-allocate-or-fail req)
         (and (stop-and-copy k v)
              (or (heap-allocate-or-fail req)
                  (out-of-memory req TO)))))
   (define (heap-allocate-or-fail req)
     (define new-ptr (+ heap-ptr req))
     (if (> new-ptr heap-size)
       #f
       (begin0 heap-ptr
               (set! heap-ptr new-ptr))))

   (define (closure-allocate k f fvs)
     (define how-many (vector-length fvs))
     (define a (heap-allocate (+ 3 how-many) k fvs))
     (heap-set! TO (+ a 0) 'closure f how-many)
     (for ([i (in-naturals)]
           [fv (in-vector fvs)])
       (heap-set! TO (+ a 3 i) fv))
     (return k a))
   (define (closure? a)
     (eq? 'closure (heap-ref TO a)))
   (define (closure-code-ptr a)
     (heap-ref TO (+ a 1)))
   (define (closure-env-ref a i)
     (heap-ref TO (+ a 3 i)))

   (define (atomic-allocate k x)
     (define a (heap-allocate 2 k (vector)))
     (heap-set! TO (+ a 0) 'atomic x)
     (return k a))
   (define (atomic? a)
     (eq? 'atomic (heap-ref TO (+ a 0))))
   (define (atomic-deref a)
     (heap-ref TO (+ a 1)))

   (define (cons-allocate k f r)
     (define frv (vector f r))
     (define a (heap-allocate 3 k frv))
     (heap-set! TO (+ a 0) 'cons (vector-ref frv 0) (vector-ref frv 1))
     (return k a))
   (define (cons? a)
     (eq? 'cons (heap-ref TO (+ a 0))))
   (define (cons-first a)
     (heap-ref TO (+ a 1)))
   (define (cons-rest a)
     (heap-ref TO (+ a 2)))
   (define (cons-set-first! a nf)
     (heap-set! TO (+ a 1) nf))
   (define (cons-set-rest! a nf)
     (heap-set! TO (+ a 2) nf))

   (define (box-allocate k b)
     (define bv (vector b))
     (define a (heap-allocate 2 k bv))
     (heap-set! TO (+ a 0) 'box (vector-ref bv 0))
     (return k a))
   (define (box? a)
     (eq? 'box (heap-ref TO (+ a 0))))
   (define (box-deref a)
     (heap-ref TO (+ a 1)))
   (define (box-set! a nb)
     (heap-set! TO (+ a 1) nb))))

(provide (all-defined-out))
