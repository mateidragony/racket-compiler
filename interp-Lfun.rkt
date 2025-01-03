#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(require "interp-Lstruct.rkt")
(provide interp-Lfun interp-Lfun-class)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define interp-Lfun-class
  (class interp-Lstruct-class
    (super-new)

    (define/override (apply-fun fun-val arg-vals e)
      (match fun-val
        [(Function xs body fun-env)
         (define params-args (for/list ([x xs] [arg arg-vals])
                               (cons x (box arg))))
         (define new-env (append params-args fun-env))
         ((interp-exp new-env) body)]
        [else (super apply-fun fun-val arg-vals e)]))
    
    (define/override ((interp-exp env) e)
      (define recur (interp-exp env))
      (verbose "Lfun/interp-exp" e)
      (match e
        [(Apply fun args)
         (define fun-val (recur fun))
         (define arg-vals (for/list ([e args]) (recur e)))
         (apply-fun fun-val arg-vals e)]
        [else ((super interp-exp env) e)]))

    (define/override (interp-def d)
      (match d
        [(Def f (list `[,xs : ,ps] ...) rt _ body)
         (list (cons f (box (Function xs body '()))))]
        [else (super interp-def d)]
        ))

    (define/override (interp-program p)
      (verbose "interp-Lfun" p)
      (match p
        [(Program info e) ((interp-exp '()) e)]
        [(ProgramDefsExp info ds body)
         (let ([top-level (foldr (λ (d r) (append (interp-def d) r)) '() ds)])
           (for/list ([f (in-dict-values top-level)])
             (set-box! f (match (unbox f)
                           [(Function xs body '())
                            (Function xs body top-level)])))
           ((interp-exp top-level) body))]
        
        ;; For after the shrink pass.
        [(ProgramDefs info ds)
         (define top-level (foldr (λ (d r) (append (interp-def d) r)) '() ds))
         (for ([f (in-dict-values top-level)])
           (set-box! f (match (unbox f)
                         [(Function xs body '())
                          (Function xs body top-level)])))
         ;; call the main function
         ((interp-exp top-level) (Apply (Var 'main) '()))]
        ))
    ))

(define (interp-Lfun p)
  (send (new interp-Lfun-class) interp-program p))
