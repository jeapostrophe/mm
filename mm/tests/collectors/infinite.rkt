#lang racket/base
(require data/gvector
         mm)

(define infinite-heap-collector@
  (collector
   (define HEAP (make-gvector))
   (define (gvector->disp g)
     (for/list ([i (in-naturals)]
                [e (in-gvector g)])
       (cons i e)))

   ;; Uses
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

(provide (all-defined-out))
