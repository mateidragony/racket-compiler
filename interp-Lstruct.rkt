#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(require "interp-Lvecof.rkt")
(provide interp-Lstruct interp-Lstruct-class)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define interp-Lstruct-class
  (class interp-Lvecof-class
    (super-new)

    (define/public (apply-fun fun-val arg-vals e)
      (match fun-val
        [(StructFunction method struct-args)
         (match method
           ['init (apply vector arg-vals)]
           ['set! (apply vector-set! (list (first arg-vals) (first struct-args) (second arg-vals)))]
           ['ref  (apply vector-ref (list (first arg-vals) (first struct-args)))])]
        [else (error 'interp-exp "expected function, not ~a\nin ~v"
                     fun-val e)]))
    
    (define/override ((interp-exp env) e)
      (define recur (interp-exp env))
      (verbose "Lstruct/interp-exp" e)
      (match e
        [(Apply fun args)
         (define fun-val (recur fun))
         (define arg-vals (for/list ([e args]) (recur e)))
         #;(apply (dict-ref env fun) arg-vals)
         (apply-fun fun-val arg-vals e)]
        [else ((super interp-exp env) e)]))

    (define/public (interp-def d)
      (match d
        [(StructDef s (list `[,xs : ,ps] ...)) 
         (append (list (cons s (box (StructFunction 'init '()))))
                 (let ((i -1))
                   (for/list [(x xs)] (cons (symbol-append 'set- (symbol-append s (symbol-append '- (symbol-append x '!))))
                                            (begin
                                              (set! i (add1 i))
                                              (box (StructFunction 'set! (list i)))))))
                 (let ((i -1))
                   (for/list [(x xs)] (cons (symbol-append s (symbol-append '- x))
                                            (begin
                                              (set! i (add1 i))
                                              (box (StructFunction 'ref (list i))))))))]))

    (define/override (interp-program p)
      (verbose "interp-Lstruct" p)
      (match p
        [(ProgramDefsExp info ds body)
         (let ([top-level (foldr (λ (d r) (append (interp-def d) r)) '() ds)])
           (for/list ([f (in-dict-values top-level)])
             (set-box! f (match (unbox f)
                           [(Function xs body '())
                            (Function xs body top-level)]
                           [e e])))
           ((interp-exp top-level) body))]
        [(Program info e) ((interp-exp '()) e)]
        ))
    ))

(define (interp-Lstruct p)
  (send (new interp-Lstruct-class) interp-program p))
