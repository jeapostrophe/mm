#lang racket/base
(require racket/match
         racket/list
         mm)

(define (generic-ms@ heap-size)
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
     (define tag (heap-ref HEAP a))
     (unless (regexp-match #rx"^marked-" (symbol->string tag))
       (heap-set! HEAP a (string->symbol (format "marked-~a" tag)))
       (define desc (hash-ref DATA tag))
       (mark-desc desc (+ a 1))))

   (define (mark-desc d a)
     (unless (empty? d)
       (match (first d)
         ['atomic
          (mark-desc (rest d) (+ a 1))]
         ['pointer
          (mark-addr (heap-ref HEAP a))
          (mark-desc (rest d) (+ a 1))]
         ['(listof . pointer)
          (define how-many (heap-ref HEAP a))
          (for ([i (in-range how-many)])
            (mark-addr (heap-ref HEAP (+ 1 a i))))])))

   ;; This "free list" is really lame
   (define (sweep)
     (sweep-from 0))
   (define (sweep-from a)
     (when (< a heap-size)
       (define tag (heap-ref HEAP a))
       (match tag
         [(== FREE)
          (sweep-from (+ a 1))]
         [(app symbol->string (regexp #rx"^marked-(.+)"
                                      (list _ (app string->symbol utag))))
          (heap-set! HEAP a utag)
          (sweep-from (+ a 1 (desc-size (hash-ref DATA utag) (add1 a))))]         
         [tag
          (define d (hash-ref DATA tag))
          (heap-set! HEAP a FREE)
          (define s (desc-size d (add1 a)))
          (desc-free d (+ a 1))
          (sweep-from (+ a 1 s))])))
   (define (desc-free d a)
     (unless (empty? d)
       (match (first d)
         ['atomic
          (heap-set! HEAP a FREE)
          (desc-free (rest d) (+ a 1))]
         ['pointer
          (heap-set! HEAP a FREE)
          (desc-free (rest d) (+ a 1))]
         ['(listof . pointer)
          (define how-many (heap-ref HEAP a))
          (heap-set!n HEAP a (add1 how-many) FREE)])))
   (define (desc-size d a)
     (if (empty? d)
       0
       (match (first d)
         [(or 'pointer 'atomic)
          (add1 (desc-size (rest d) (+ a 1)))]
         ['(listof . pointer)
          (define how-many (heap-ref HEAP a))
          (add1 how-many)])))

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

   (define (desc-allocate tag d fs)
     (for/fold ([size 1]
                [roots null]
                [install!
                 (λ (a rs)
                   (heap-set! HEAP a tag))])
         ([e (in-list d)]
          [f (in-list fs)])
       (match e
         ['atomic
          (values (+ size 1)
                  roots
                  (λ (a rs)
                    (heap-set! HEAP (+ a size) f)
                    (install! a rs)))]
         ['pointer
          (values (+ size 1)
                  (cons f roots)
                  (λ (a rs)
                    (heap-set! HEAP (+ a size) (car rs))
                    (install! a (rest rs))))]
         ['(listof . pointer)
          (define how-many (vector-length f))
          (values (+ size 1 how-many)
                  (append (vector->list f) roots)
                  (λ (a rs)
                    (define-values (pre post) (split-at rs how-many))
                    (heap-set!* HEAP (+ a size) how-many pre)
                    (install! a post)))])))

   (define DATA (make-hasheq))
   (define (data! tag desc)
     (hash-set! DATA tag desc))
   (define (allocate tag)
     (define desc (hash-ref DATA tag))
     (λ (k . fs)
       (define-values (req vsl install!) (desc-allocate tag desc fs))
       (define vs (list->vector vsl))
       (define a (heap-allocate req k vs))
       (install! a (vector->list vs))
       (return k a)))
   (define (identify tag)
     (λ (a)
       (eq? tag (heap-ref HEAP a))))
   (define (field tag fi)
     (define desc (hash-ref DATA tag))
     (λ (a)
       (heap-ref HEAP (+ 1 a fi))))
   (define (mutate tag fi)
     (define desc (hash-ref DATA tag))
     (λ (a v)
       (heap-set! HEAP (+ 1 a fi) v)))
   (define (fieldi tag fi)
     (define desc (hash-ref DATA tag))
     (λ (a i)
       (heap-ref HEAP (+ 1 a fi 1 i))))

   (data! 'closure
          (list 'atomic '(listof . pointer)))

   (define closure-allocate (allocate 'closure))
   (define closure? (identify 'closure))
   (define closure-code-ptr (field 'closure 0))
   (define closure-env-ref (fieldi 'closure 1))

   (data! 'atomic
          (list 'atomic))

   (define atomic-allocate (allocate 'atomic))
   (define atomic? (identify 'atomic))
   (define atomic-deref (field 'atomic 0))

   (data! 'cons
          (list 'pointer 'pointer))

   (define cons-allocate (allocate 'cons))
   (define cons? (identify 'cons))
   (define cons-first (field 'cons 0))
   (define cons-rest (field 'cons 1))
   (define cons-set-first! (mutate 'cons 0))
   (define cons-set-rest! (mutate 'cons 1))

   (data! 'box
          (list 'pointer))

   (define box-allocate (allocate 'box))
   (define box? (identify 'box))
   (define box-deref (field 'box 0))
   (define box-set! (mutate 'box 0))))

(provide generic-ms@)
