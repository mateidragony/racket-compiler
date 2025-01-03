#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "type-check-Llambda.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lvecof.rkt")
(require "interp-Lstruct.rkt")
(require "interp-Lfun.rkt")
(require "interp-Llambda.rkt")
(require "interp-Ldyn.rkt")
(require "interp.rkt")
(require "compiler.rkt")

(debug-level 0)
(AST-output-syntax 'abstract-syntax)
;;(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

(define (one-test t n [tc #f])
  (interp-tests t tc compiler-passes interp-Ldyn (string-append t "_test") (list (number->string n))))

(define (one-test-compiler t n)
  (compiler-tests t #f compiler-passes (string-append t "_test") (list (number->string n))))

;; ;; One tests for debugging
;; (one-test "dynamic" 43)
;; (one-test-compiler "dynamic" 43)

;; The following tests the intermediate-language outputs of the passes.
(interp-tests "var" #f compiler-passes interp-Ldyn "var_test" (tests-for "var"))
(interp-tests "pe" #f compiler-passes interp-Ldyn "pe_test" (tests-for "pe"))
(interp-tests "cond" #f compiler-passes interp-Ldyn "cond_test" (tests-for "cond"))
(interp-tests "while" #f compiler-passes interp-Ldyn "while_test" (tests-for "while"))
(interp-tests "vectors" #f compiler-passes interp-Lvec "vectors_test" (tests-for "vectors"))
(interp-tests "propogate" #f compiler-passes interp-Lvec "propogate_test" (tests-for "propogate"))
;; (interp-tests "vecof" #f compiler-passes interp-Lvecof "vecof_test" (tests-for "vecof"))
;; (interp-tests "struct" #f compiler-passes interp-Lstruct "struct_test" (tests-for "struct"))
;; (interp-tests "functions" #f compiler-passes interp-Lfun "functions_test" (tests-for "functions"))
;; (interp-tests "lambda" #f compiler-passes interp-Llambda "lambda_test" (tests-for "lambda"))
;; (interp-tests "optlambda" #f compiler-passes interp-Llambda "optlambda_test" (tests-for "optlambda"))
(interp-tests "dynamic" #f compiler-passes interp-Ldyn "dynamic_test" (tests-for "dynamic"))

;; ;; The following tests the final x86 code.
(compiler-tests "var" #f compiler-passes "var_test" (tests-for "var"))
(compiler-tests "pe" #f compiler-passes "pe_test" (tests-for "pe"))
(compiler-tests "cond" #f compiler-passes "cond_test" (tests-for "cond"))
(compiler-tests "while" #f compiler-passes "while_test" (tests-for "while"))
(compiler-tests "vectors" #f compiler-passes "vectors_test" (tests-for "vectors"))
(compiler-tests "propogate" #f compiler-passes "propogate_test" (tests-for "propogate"))
;; (compiler-tests "vecof" #f compiler-passes "vecof_test" (tests-for "vecof"))
;; (compiler-tests "struct" #f compiler-passes "struct_test" (tests-for "struct"))
;; (compiler-tests "functions" #f compiler-passes "functions_test" (tests-for "functions"))
;; (compiler-tests "lambda" #f compiler-passes "lambda_test" (tests-for "lambda"))
;; (compiler-tests "optlambda" #f compiler-passes "optlambda_test" (tests-for "optlambda"))
(compiler-tests "dynamic" #f compiler-passes "dynamic_test" (tests-for "dynamic"))
