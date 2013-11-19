#lang racket/base
(require racket/contract
         racket/match
         "heap-gui.rkt"
         "collector.rkt")

(define FREE (gensym 'free))

(struct heap (v gui))

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
  (heap v gui))

(define (heap-ref h a)
  (vector-ref (heap-v h) a))

(define (heap-set! h a . vs)
  (for ([v (in-list vs)]
        [i (in-naturals)])
    (vector-set! (heap-v h) (+ a i) v))
  ((heap-gui h)))

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
       void?)]
  [make-heap
   (-> exact-nonnegative-integer?
       heap?)]))
