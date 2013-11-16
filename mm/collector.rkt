#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/unit-exptime)
         racket/list
         racket/unit
         racket/contract
         "runtime.rkt")

;; xxx optional functions

(define heap-value/c
  (or/c number? boolean? empty? void? string? symbol? code-ptr?))

(define contract-collector@
  (unit (import (prefix in: collector^))
        (export collector^)

        (define-syntax (defc stx)
          (syntax-parse stx
            [(_ id ctc)
             (with-syntax ([in:id (format-id #'id "in:~a" #'id)])
               (syntax/loc stx
                 (define id (contract ctc in:id
                                      'collector 'mutator-internals
                                      'id #f))))]))
        (define-syntax-rule (defc* [id ctc] ...)
          (begin (defc id ctc) ...))

        (defc*
          [closure-allocate
           (-> stack? code-ptr? (vectorof heap-addr?)
               return?)]
          [closure?
           (-> heap-addr?
               boolean?)]
          [closure-code-ptr
           (-> heap-addr?
               code-ptr?)]
          [closure-env-ref
           (-> heap-addr? exact-nonnegative-integer?
               heap-addr?)]
          [box-allocate
           (-> stack? heap-addr?
               return?)]
          [box?
           (-> heap-addr?
               boolean?)]
          [box-deref
           (-> heap-addr?
               heap-addr?)]
          [box-set!
           (-> heap-addr? heap-addr?
               void?)]
          [atomic-allocate
           (-> stack? heap-value/c
               return?)]
          [atomic?
           (-> heap-addr?
               boolean?)]
          [atomic-deref
           (-> heap-addr?
               heap-value/c)]
          [cons-allocate
           (-> stack? heap-addr? heap-addr?
               return?)]
          [cons?
           (-> heap-addr?
               boolean?)]
          [cons-first
           (-> heap-addr?
               heap-addr?)]
          [cons-rest
           (-> heap-addr?
               heap-addr?)]
          [cons-set-first!
           (-> heap-addr? heap-addr?
               void?)]
          [cons-set-rest!
           (-> heap-addr? heap-addr?
               void?)])))

(define (collector/contracts collector@)
  (compound-unit
   (import) (export CTC)
   (link [([C : collector^]) collector@]
         [([CTC : collector^]) contract-collector@ C])))

(define-syntax (collector stx)
  (syntax-case stx ()
    [(_ e ...)
     (with-syntax
         ([([i-export e-export] ...)
           (let-values ([(_1 ids _2 _3) (signature-members #'collector^ stx)])
             (for/list ([i (in-list ids)])
               (list i (datum->syntax stx (syntax->datum i)))))])
       (syntax/loc stx
         (collector/contracts
          (unit (import) (export collector^)
                e ...
                (define i-export e-export)
                ...))))]))

(provide
 heap-value/c
 collector
 (except-out (all-from-out "runtime.rkt")
             collector^
             mutator-run))
