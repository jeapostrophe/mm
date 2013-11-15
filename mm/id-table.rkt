#lang racket/base
(require racket/list
         syntax/id-table
         racket/dict)
(provide (all-defined-out))

(define empty-id-table (make-immutable-free-id-table empty))
(define-syntax-rule (id-set [k v] ...)
  (make-immutable-free-id-table (list (cons #'k #'v) ...)))

(define (list->id-set ks)
  (for/fold ([ids empty-id-table])
      ([k (in-list (if (syntax? ks) (syntax->list ks) ks))])
    (dict-set ids k #t)))
(define (id-set-union ids-l)
  (for*/fold ([all-ids empty-id-table])
      ([next-ids (in-list ids-l)]
       [next-id (in-dict-keys next-ids)])
    (dict-set all-ids next-id #t)))
(define (id-set->list ids)
  (for/list ([k (in-dict-keys ids)])
    k))
(define (id-set-remove ids lst)
  (for/fold ([ids ids])
      ([k (in-list (if (syntax? lst) (syntax->list lst) lst))])
    (dict-remove ids k)))
