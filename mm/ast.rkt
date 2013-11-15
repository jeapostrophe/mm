#lang racket/base

(struct mutator-atomic (value))
(struct mutator-primitive (prim-id args))
(struct mutator-lambda (params body))
(struct mutator-id (id))
(struct mutator-apply (fun args))
(struct mutator-apply1 (fun arg))
(struct mutator-if (test then else))

;; xxx add contracts
(provide (all-defined-out))
