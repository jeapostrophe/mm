#lang racket/base
(require racket/contract
         racket/match
         "heap-gui.rkt"
         "collector.rkt")

(define FREE (gensym 'free))

(struct heap ())
(struct heap:raw heap (v gui))
(struct heap:slice heap (parent from size))

;; xxx move these to runtime so I can visualize the stack as well and
;; integrate the stepper deeper
(define visualize? (make-parameter #f))
(define stepper? (make-parameter #f))
(define-syntax-rule (visualize . e)
  (parameterize ([visualize? #t])
    . e))
(define-syntax-rule (visualize/stepper . e)
  (parameterize ([stepper? #t])
    (visualize . e)))

(define (make-heap size)
  (define v (make-vector size FREE))
  (define gui
    (if (visualize?)
      (make-heap-gui (stepper?) FREE v)
      void))
  (heap:raw v gui))

(define (heap-slice parent from size)
  (define psize (heap-size parent))
  (unless (<= (+ from size) psize)
    (error 'heap-slice
           "Slice(~e:~e) is too big for parent(~e)"
           from size
           psize))
  (heap:slice parent from size))

(define heap-size
  (match-lambda
   [(heap:raw v _)
    (vector-length v)]
   [(heap:slice _ _ s)
    s]))

(define (heap-ref h a)
  (define hsize (heap-size h))
  (unless (< a hsize)
    (error 'heap-ref "Address(~e) out of range(~e)" a hsize))
  (match h
    [(heap:raw v _)
     (vector-ref v a)]
    [(heap:slice p offset _)
     (heap-ref p (+ offset a))]))

(define (heap-set! h a . vs)
  (define cnt (length vs))
  (define hsize (heap-size h))
  (unless (<= (+ a cnt) hsize)
    (error 'heap-set! "Address(~e) + value span(~e:~e) out of range(~e)"
           a cnt vs hsize))
  (match h
    [(heap:raw hv gui)
     (for ([v (in-list vs)]
           [i (in-naturals)])
       (vector-set! hv (+ a i) v))
     (gui)]
    [(heap:slice p offset _)
     (apply heap-set! p (+ offset a) vs)]))

(define (heap-set!n h a cnt v)
  (apply heap-set! h a (for/list ([i (in-range cnt)]) v)))

(define (heap-set!* h a . vs+)
  (match-define (cons last rvs) (reverse vs+))
  (define ->list
    (match-lambda
     [(? list? l)
      l]
     [(? vector? v)
      (vector->list v)]))
  (apply heap-set! h a
         (append (reverse rvs)
                 (->list last))))

(provide
 visualize
 visualize/stepper
 (contract-out
  [FREE
   symbol?]
  [heap?
   (-> any/c
       boolean?)]
  [make-heap
   (-> exact-positive-integer?
       heap?)]
  [heap-slice
   (-> heap? exact-nonnegative-integer? exact-positive-integer?
       heap?)]
  [heap-size
   (-> heap?
       exact-positive-integer?)]
  [heap-ref
   (-> heap? heap-addr?
       heap-value/c)]
  [heap-set!
   (->* (heap? heap-addr?)
        #:rest (listof heap-value/c)
        void?)]
  [heap-set!*
   (->* (heap? heap-addr?)
        ;; xxx better contract
        #:rest any/c
        void?)]
  [heap-set!n
   (-> heap? heap-addr? exact-nonnegative-integer? heap-value/c
       void?)]))
