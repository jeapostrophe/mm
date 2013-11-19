#lang racket/base
(require racket/match
         mm)

(define (mark-and-sweep@ heap-size)
  (collector
   (define HEAP (make-heap heap-size))

   (define (mark-and-sweep k v)
     (mark k v)
     (sweep))
   (define (mark k v)
     (mark-stack k)
     (mark-vector v))
   (define (mark-stack k)
     (unless (stack-bot? k)
       (mark-vector (stack-frame-locals k))
       (mark-stack (stack-frame-parent k))))
   (define (mark-vector v)
     (for ([a (in-vector v)])
       (mark-addr a)))
   (define (mark-addr a)
     (match (heap-ref HEAP a)
       [(or 'ATOMIC 'BOX 'CONS 'CLOSURE)
        (void)]
       ['atomic
        (heap-set! HEAP (+ a 0) 'ATOMIC)]
       ['box
        (heap-set! HEAP (+ a 0) 'BOX)
        (mark-addr (heap-ref HEAP (+ a 1)))]
       ['cons
        (heap-set! HEAP (+ a 0) 'CONS)
        (mark-addr (heap-ref HEAP (+ a 1)))
        (mark-addr (heap-ref HEAP (+ a 2)))]
       ['closure
        (heap-set! HEAP (+ a 0) 'CLOSURE)
        (define how-many (heap-ref HEAP (+ a 2)))
        (for ([i (in-range how-many)])
          (mark-addr (heap-ref HEAP (+ a 3 i))))]
       [tag
        (error 'mark-addr "Unknown tag ~e @ ~a in: ~a" tag a HEAP)]))

   ;; This "free list" is really lame
   (define (sweep)
     (sweep-from 0))
   (define (sweep-from a)
     (when (< a heap-size)
       (match (heap-ref HEAP a)
         ['closure
          (define how-many (heap-ref HEAP (+ a 2)))
          (heap-set! HEAP (+ a 0) FREE FREE FREE)
          (heap-set!n HEAP (+ a 3) how-many FREE)
          (sweep-from (+ a 3 how-many))]
         ['CLOSURE
          (define how-many (heap-ref HEAP (+ a 2)))
          (heap-set! HEAP (+ a 0) 'closure)
          (sweep-from (+ a 3 how-many))]
         ['atomic
          (heap-set! HEAP (+ a 0) FREE FREE)
          (sweep-from (+ a 2))]
         ['ATOMIC
          (heap-set! HEAP (+ a 0) 'atomic)
          (sweep-from (+ a 2))]
         ['cons
          (heap-set! HEAP (+ a 0) FREE FREE FREE)
          (sweep-from (+ a 3))]
         ['CONS
          (heap-set! HEAP (+ a 0) 'cons)
          (sweep-from (+ a 3))]
         ['box
          (heap-set! HEAP (+ a 0) FREE FREE)
          (sweep-from (+ a 2))]
         ['BOX
          (heap-set! HEAP (+ a 0) 'box)
          (sweep-from (+ a 2))]
         [(== FREE)
          (sweep-from (+ a 1))]
         [tag
          (error 'sweep-from "Unknown tag ~e @ ~a in: ~a" tag a HEAP)])))

   (define (heap-allocate req k v)
     (or (heap-allocate-or-fail req)
         (and (mark-and-sweep k v)
              (or (heap-allocate-or-fail req)
                  (out-of-memory req HEAP)))))
   (define (heap-allocate-or-fail req)
     (for/or ([start (in-range 0 (- heap-size req -1))])
       (and (for/and ([block (in-range req)])
              (eq? FREE (heap-ref HEAP (+ start block))))
            start)))

   (define (closure-allocate k f fvs)
     (define how-many (vector-length fvs))
     (define a (heap-allocate (+ 3 how-many) k fvs))
     (heap-set!* HEAP (+ a 0) 'closure f how-many fvs)
     (return k a))
   (define (closure? a)
     (eq? 'closure (heap-ref HEAP a)))
   (define (closure-code-ptr a)
     (heap-ref HEAP (+ a 1)))
   (define (closure-env-ref a i)
     (heap-ref HEAP (+ a 3 i)))

   (define (atomic-allocate k x)
     (define a (heap-allocate 2 k (vector)))
     (heap-set! HEAP (+ a 0) 'atomic x)
     (return k a))
   (define (atomic? a)
     (eq? 'atomic (heap-ref HEAP (+ a 0))))
   (define (atomic-deref a)
     (heap-ref HEAP (+ a 1)))

   (define (cons-allocate k f r)
     (define frv (vector f r))
     (define a (heap-allocate 3 k frv))
     (heap-set!* HEAP (+ a 0) 'cons frv)
     (return k a))
   (define (cons? a)
     (eq? 'cons (heap-ref HEAP (+ a 0))))
   (define (cons-first a)
     (heap-ref HEAP (+ a 1)))
   (define (cons-rest a)
     (heap-ref HEAP (+ a 2)))
   (define (cons-set-first! a nf)
     (heap-set! HEAP (+ a 1) nf))
   (define (cons-set-rest! a nf)
     (heap-set! HEAP (+ a 2) nf))

   (define (box-allocate k b)
     (define bv (vector b))
     (define a (heap-allocate 2 k bv))
     (heap-set!* HEAP (+ a 0) 'box bv)
     (return k a))
   (define (box? a)
     (eq? 'box (heap-ref HEAP (+ a 0))))
   (define (box-deref a)
     (heap-ref HEAP (+ a 1)))
   (define (box-set! a nb)
     (heap-set! HEAP (+ a 1) nb))))

(provide (all-defined-out))
