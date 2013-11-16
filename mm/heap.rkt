#lang racket/base
(require racket/contract
         "heap-gui.rkt"
         "collector.rkt")

(define FREE (gensym 'free))

(struct heap (v gui)
        #:property prop:procedure
        (case-lambda
          [(h a)
           (vector-ref (heap-v h) a)]
          [(h a . vs)
           (for ([v (in-list vs)]
                 [i (in-naturals)])
             (vector-set! (heap-v h) (+ a i) v))
           ((heap-gui h))]))

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
   (-> exact-nonnegative-integer?
       (case->
        (-> heap-addr?
            heap-value/c)
        (-> heap-addr? #:rest (listof heap-value/c)
            void?)))]))
