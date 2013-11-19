#lang racket/base
(module+ test
  (require "suite.rkt"
           "collectors/infinite.rkt"
           "collectors/mark-and-sweep.rkt"
           "collectors/stop-and-copy.rkt")

  (run-suite (λ (size) infinite-heap-collector@))
  (run-suite mark-and-sweep@)
  (run-suite stop-and-copy@))
