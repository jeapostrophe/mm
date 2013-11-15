#lang racket/base
(require "id-table.rkt"
         racket/match)

(struct mutator-atomic (value))
(struct mutator-primitive (prim-id args))
(struct mutator-lambda (params body))
(struct mutator-id (id))
(struct mutator-apply (fun args))
(struct mutator-apply1 (fun arg))
(struct mutator-if (test then else))

(define (mutator-free-vars me)
  (id-set->list
   (let loop ([me me])
     (match me
       [(mutator-atomic _)
        empty-id-table]
       [(mutator-primitive _ args)
        (id-set-union (map loop args))]
       [(mutator-lambda ids body)
        (id-set-remove (loop body) ids)]
       [(mutator-id id)
        (list->id-set (list id))]
       [(mutator-apply fun args)
        (id-set-union (cons (loop fun) (map loop args)))]
       [(mutator-apply1 fun arg)
        (id-set-union (map loop (list fun arg)))]
       [(mutator-if test then else)
        (id-set-union (map loop (list test then else)))]))))

;; xxx add contracts
(provide (all-defined-out))
