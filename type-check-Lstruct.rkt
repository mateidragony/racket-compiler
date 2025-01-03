#lang racket
(require "utilities.rkt")
(require "type-check-Lvecof.rkt")
(provide type-check-Lstruct
         type-check-Lstruct-class)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Structs as Syntactic Sugar                                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-Lstruct

(define type-check-Lstruct-class
  (class  type-check-Lvecof-class
    (super-new)
    (inherit check-type-equal?
             combine-types)

    (define/public (struct-def-type d)
      (match d
        [(StructDef s (list `[,xs : ,ps] ...)) (map cons xs ps)]
        [else (error 'type-check "ill-formed function definition in ~a" d)]))
    
    (define/override (type-check-exp env)
      (lambda (e)
        (match e
          [(Apply var exps) ; either, vector, vetor-ref, or set!
           (define ss (string-split (symbol->string var) "-"))
           ;; See if it's a struct def
           ;; is a struct-name
           (cond
             ;; Struct assignment
             ;; starts with set-{struct-nam}-{filed}  ex. (Apply 'set-point-x! (list pt 42))
             [(and (equal? (first ss) "set") (dict-has-key? env (string->symbol (second ss))))
              ;; remove !
              (define field-ref (string->symbol (substring (third ss) 0 (sub1 (string-length (third ss))))))
              (define struc (string->symbol (second ss)))
              ;; get the index of field-ref
              (define i (index-where (dict-ref env struc) (lambda (p) (eqv? (car p) field-ref))))
              ;; get the type of field-ref, and make sure it works
              ((type-check-exp env) (Prim 'vector-set! (list (first exps) (Int i) (second exps))))]
             [(dict-has-key? env (string->symbol (first ss)))
              (cond
                ;; Struct instantiation
                [(eq? 1 (length ss))
                 (define n (string->symbol (first ss)))
                 ((type-check-exp env) (Prim 'vector exps))]
                ;; Struct reference
                [else
                 (define field-ref (string->symbol (cadr ss)))
                 (define struc (string->symbol (cadr ss)))
                 ;; get the index of field-ref
                 (define i (index-where (dict-ref env struc) (lambda (p) (eqv? (car p) (field-ref)))))
                 ;; get the type of field-ref, and make sure it works
                 ((type-check-exp env) (Prim 'vector-ref (list (car exps) (Int i))))])]
             [else (error "Typecheck struct, expected a field reference")])]
          [else ((super type-check-exp env) e)])))
    (define/override (type-check-program e)
      (match e
        [(ProgramDefsExp info ds body)
         (define new-env
           (for/list ([d ds])
             (cons (StructDef-name d) (struct-def-type d))))
         (define-values (body^ ty) ((type-check-exp new-env) body))
         (check-type-equal? ty 'Integer body)
         (Program info body^)]
        [(Program info body)
         (define-values (body^ ty) ((type-check-exp '()) body))
         (check-type-equal? ty 'Integer body)
         (ProgramDefsExp info '() body^)]
        [else (error 'type-check "unrecognized ~a" e)]))))

(define (type-check-Lstruct p)
  (send (new type-check-Lstruct-class) type-check-program p))
