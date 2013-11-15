#lang racket/base
(require racket/match
         mm)

(define (mark-and-sweep@ heap-size)
  (collector
   (define FREE (gensym))
   (define HEAP (make-vector heap-size FREE))

   (define (mark-and-sweep k v)
     (mark k v)
     (sweep))
   (define (mark k v)
     (mark-stack k)
     (mark-vector v))
   (define (mark-stack k)
     (unless (stack-bot? k)
       (mark-vector (stack-frame-env-addrs k))
       (mark-stack (stack-frame-parent k))))
   (define (mark-vector v)
     (for ([a (in-vector v)])
       (mark-addr a)))
   (define (mark-addr a)
     (match (vector-ref HEAP a)
       [(or 'ATOMIC 'BOX 'CONS 'CLOSURE)
        (void)]
       ['atomic
        (vector-set! HEAP (+ a 0) 'ATOMIC)]
       ['box
        (vector-set! HEAP (+ a 0) 'BOX)
        (mark-addr (vector-ref HEAP (+ a 1)))]
       ['cons
        (vector-set! HEAP (+ a 0) 'CONS)
        (mark-addr (vector-ref HEAP (+ a 1)))
        (mark-addr (vector-ref HEAP (+ a 2)))]
       ['closure
        (vector-set! HEAP (+ a 0) 'CLOSURE)
        (define how-many (vector-ref HEAP (+ a 2)))
        (for ([i (in-range how-many)])
          (mark-addr (vector-ref HEAP (+ a 3 i))))]
       [tag
        (error 'mark-addr "Unknown tag ~e @ ~a in: ~a" tag a HEAP)]))

   ;; This "free list" is really lame
   (define (sweep)
     (sweep-from 0))
   (define (sweep-from a)
     (when (< a heap-size)
       (match (vector-ref HEAP a)
         ['closure
          (vector-set! HEAP (+ a 0) FREE)
          (vector-set! HEAP (+ a 1) FREE)
          (define how-many (vector-ref HEAP (+ a 2)))
          (vector-set! HEAP (+ a 2) FREE)
          (for ([i (in-range how-many)])
            (vector-set! HEAP (+ a 3 i) FREE))
          (sweep-from (+ a 3 how-many))]
         ['CLOSURE
          (vector-set! HEAP (+ a 0) 'closure)
          (define how-many (vector-ref HEAP (+ a 2)))
          (sweep-from (+ a 3 how-many))]
         ['atomic
          (vector-set! HEAP (+ a 0) FREE)
          (vector-set! HEAP (+ a 1) FREE)
          (sweep-from (+ a 2))]
         ['ATOMIC
          (vector-set! HEAP (+ a 0) 'atomic)
          (sweep-from (+ a 2))]
         ['cons
          (vector-set! HEAP (+ a 0) FREE)
          (vector-set! HEAP (+ a 1) FREE)
          (vector-set! HEAP (+ a 2) FREE)
          (sweep-from (+ a 3))]
         ['CONS
          (vector-set! HEAP (+ a 0) 'cons)
          (sweep-from (+ a 3))]
         ['box
          (vector-set! HEAP (+ a 0) FREE)
          (vector-set! HEAP (+ a 1) FREE)
          (sweep-from (+ a 2))]
         ['BOX
          (vector-set! HEAP (+ a 0) 'box)
          (sweep-from (+ a 2))]
         [(== FREE)
          (sweep-from (+ a 1))]
         [tag
          (error 'sweep-from "Unknown tag ~e @ ~a in: ~a" tag a HEAP)])))

   (define (heap-allocate req k v)
     (or (heap-allocate-or-fail req)
         (and (mark-and-sweep k v)
              (or (heap-allocate-or-fail req)
                  (error 'heap-allocate "Heap is too full for ~a: ~a" req HEAP)))))
   (define (heap-allocate-or-fail req)
     (for/or ([start (in-range 0 (- heap-size req -1))])
       (and (for/and ([block (in-range req)])
              (eq? FREE (vector-ref HEAP (+ start block))))
            start)))

   (define (closure-allocate k f fvs)
     (define how-many (vector-length fvs))
     (define a (heap-allocate (+ 3 how-many) k fvs))
     (vector-set! HEAP (+ a 0) 'closure)
     (vector-set! HEAP (+ a 1) f)
     (vector-set! HEAP (+ a 2) how-many)
     (for ([i (in-naturals)]
           [fv (in-vector fvs)])
       (vector-set! HEAP (+ a 3 i) fv))
     (return k a))
   (define (closure? a)
     (eq? 'closure (vector-ref HEAP a)))
   (define (closure-code-ptr a)
     (vector-ref HEAP (+ a 1)))
   (define (closure-env-ref a i)
     (vector-ref HEAP (+ a 3 i)))

   (define (atomic-allocate k x)
     (define a (heap-allocate 2 k (vector)))
     (vector-set! HEAP (+ a 0) 'atomic)
     (vector-set! HEAP (+ a 1) x)
     (return k a))
   (define (atomic? a)
     (eq? 'atomic (vector-ref HEAP (+ a 0))))
   (define (atomic-deref a)
     (vector-ref HEAP (+ a 1)))

   (define (cons-allocate k f r)
     (define frv (vector f r))
     (define a (heap-allocate 3 k frv))
     (vector-set! HEAP (+ a 0) 'cons)
     (vector-set! HEAP (+ a 1) (vector-ref frv 0))
     (vector-set! HEAP (+ a 2) (vector-ref frv 1))
     (return k a))
   (define (cons? a)
     (eq? 'cons (vector-ref HEAP (+ a 0))))
   (define (cons-first a)
     (vector-ref HEAP (+ a 1)))
   (define (cons-rest a)
     (vector-ref HEAP (+ a 2)))
   (define (cons-set-first! a nf)
     (vector-set! HEAP (+ a 1) nf))
   (define (cons-set-rest! a nf)
     (vector-set! HEAP (+ a 2) nf))

   (define (box-allocate k b)
     (define bv (vector b))
     (define a (heap-allocate 2 k bv))
     (vector-set! HEAP (+ a 0) 'box)
     (vector-set! HEAP (+ a 1) (vector-ref bv 0))
     (return k a))
   (define (box? a)
     (eq? 'box (vector-ref HEAP (+ a 0))))
   (define (box-deref a)
     (vector-ref HEAP (+ a 1)))
   (define (box-set! a nb)
     (vector-set! HEAP (+ a 1) nb))))

(module+ test
  (require rackunit/chk
           racket/list)

  (chk (mutator-run
        (mark-and-sweep@ 6)
        (mutator 1 2 3))
       3)
  (chk (mutator-run
        (mark-and-sweep@ 7)
        (mutator 1 2 3 (cons 4 5)))
       (cons 4 5))
  (chk (mutator-run
        (mark-and-sweep@ 10)
        (mutator 1 2 3 (cons 4 5) 6))
       6)
  (chk (mutator-run
        (mark-and-sweep@ 12)
        (mutator 1 2 3 (cons (cons 4 5) 6)))
       (cons (cons 4 5) 6))
  (chk (mutator-run
        (mark-and-sweep@ 7)
        (mutator (box 1) 2))
       2)
  (chk (mutator-run
        (mark-and-sweep@ 9)
        (mutator (cons (box 1) 2)))
       (cons (box 1) 2))
  (chk (mutator-run
        (mark-and-sweep@ 15)
        (mutator (define x (cons 1 2))
                 (set-rest! x x)
                 3 4
                 (first x)))
       1)
  (chk (mutator-run
        (mark-and-sweep@ 50)
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
       (+ 5 (+ 1 2 3 4 5))))
