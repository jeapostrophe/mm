#lang racket/base
(require racket/list
         racket/contract)

(struct mutator-expr ())
(struct mutator-atomic mutator-expr (value))
(struct mutator-primitive mutator-expr (prim args))
(struct mutator-lambda mutator-expr (params body))
(struct mutator-id mutator-expr (id))
(struct mutator-apply mutator-expr (fun args))
(struct mutator-apply1 mutator-expr (fun arg))
(struct mutator-if mutator-expr (test then else))

(provide
 (contract-out
  (struct mutator-expr ())
  (struct (mutator-atomic mutator-expr)
          ([value (or/c number? boolean? empty? void? string? symbol?)]))
  (struct (mutator-primitive mutator-expr)
          ([prim (or/c symbol? procedure?)]
           [args (listof mutator-expr?)]))
  (struct (mutator-lambda mutator-expr)
          ([params (listof identifier?)]
           [body mutator-expr?]))
  (struct (mutator-id mutator-expr)
          ([id identifier?]))
  (struct (mutator-apply mutator-expr)
          ([fun mutator-expr?]
           [args (listof mutator-expr?)]))
  (struct (mutator-apply1 mutator-expr)
          ([fun mutator-lambda?]
           [arg mutator-expr?]))
  (struct (mutator-if mutator-expr)
          ([test mutator-expr?]
           [then mutator-expr?]
           [else mutator-expr?]))))
