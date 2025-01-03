#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "interp.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.

(define (collapseable-let? e)
  (match e
    [(Int n) #t]
    [(Var x) #t]
    [else #f]))

(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [(Var x) (Prim '- (list (Var x)))]
    [(Prim 'read '()) (Prim '- (list (Prim 'read '())))]
    [(Prim '+ (list i1 i2)) (Prim '+ (list (pe-neg i1) (pe-neg i2)))]
    [(Let v r1 r2) (Let v r1 (pe-neg r2))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2))
     (Int (fx+ n1 n2))]
    [((Int n1) (Prim '+ (list (Int n2) inert)))
     (Prim '+ (list (Int (fx+ n1 n2)) inert))]
    [((Prim '+ (list (Int n2) i)) (Int n1))
     (Prim '+ (list (Int (fx+ n1 n2)) i))]
    [((Prim '+ (list (Int n1) i1)) (Prim '+ (list (Int n2) i2)))
     (Prim '+ (list (Int (fx+ n1 n2)) (Prim '+ (list i1 i2))))]
    [((Int n) i)
     (Prim '+ (list (Int n) i))]
    [(i (Int n))
     (Prim '+ (list (Int n) i))]
    [((Prim '+ (list (Int n) i1)) i2)
     (Prim '+ (list (Int n) (Prim '+ (list i1 i2))))]
    [(i1 (Prim '+ (list (Int n) i2)))
     (Prim '+ (list (Int n) (Prim '+ (list i1 i2))))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e env)
  (match e
    [(Int n) (Int n)]
    [(Var x) (if (dict-has-key? env x)
                 (dict-ref env x)
                 (Var x))]
    [(Let v e1 e2)
     (define val (pe-exp e1 env))
     (if (collapseable-let? val)
         (pe-exp e2 (dict-set env v val))
         (Let v val (pe-exp e2 (dict-remove env v))))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1 env))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1 env) (pe-neg (pe-exp e2 env)))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1 env) (pe-exp e2 env))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e '()))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unique-number 0)
(define (uniquify-name x)
  (begin
    (set! unique-number (add1 unique-number))
    (string->symbol (string-append
                     (symbol->string x)
                     "."
                     (number->string unique-number)))))

(define (uniquify-exp env) ;; old name -> unique name
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let ((new-name (uniquify-name x)))
         (Let new-name
              ((uniquify-exp env) e)
              ((uniquify-exp (dict-set env x new-name)) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (begin
    (set! unique-number 0)
    (match p
      [(Program info e) (Program info ((uniquify-exp '()) e))])))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
      [(Program info e) (Program info (rco-exp e))]))

(define (rco-atom e)
  (match e
    [(Var x) (cons (Var x) '())]
    [(Int n) (cons (Int n) '())]
    [(Let x e body)
     (define tmp (uniquify-name 'tmp))
     (cons (Var tmp) (dict-set '() tmp (rco-exp (Let x e body))))]
    [(Prim op es)
     (define tmp (uniquify-name 'tmp))
     (cons (Var tmp) (dict-set '() tmp (rco-exp (Prim op es))))]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es) (primops->letexp es op '())]))

(define (primops->letexp es op args)
  (cond
    ((null? es) (Prim op (reverse args)))
    (else (let* ((ret (rco-atom (car es)))
                 (atom (car ret))
                 (mapping (cdr ret)))
            (if (null? mapping)
                (primops->letexp (cdr es) op (cons atom args))
                (match atom
                  [(Var x) (Let x (dict-ref mapping x) (primops->letexp (cdr es) op (cons atom args)))]))))))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate_assign rhs x (explicate-tail body))]
    [(Prim op es) (Return (Prim op es))]))

(define (explicate_assign e x cont)
  (match e
    [(Var x^) (Seq (Assign (Var x) (Var x^)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]))

(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info `((start . ,(explicate-tail body))))]))

;; select-instructions : Cvar -> x86var
(define (select-atm e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    [else (error "Not an atom")]))

(define (select-stmt x e)
  (match e
    [(Prim 'read '())
     (list (Callq 'read_int 0)
           (Instr 'movq `(,(Reg 'rax) ,x)))]
    [(Prim '- `(,a))
     (if (eq? a x)
         (list (Instr 'negq `(,x)))
         (list (Instr 'movq `(,(select-atm a) ,x))
               (Instr 'negq `(,x))))]
    [(Prim '+ `(,a1 ,a2))
     (cond
       ((eq? a1 x) (list (Instr 'addq `(,(select-atm a2) ,x))))
       ((eq? a2 x) (list (Instr 'addq `(,(select-atm a1) ,x))))
       (else (list (Instr 'movq `(,(select-atm a1) ,x))
                   (Instr 'addq `(,(select-atm a2) ,x)))))]
    [(Prim '- `(,a1 ,a2))
     (cond
       ((eq? a1 x) (list (Instr 'subq `(,(select-atm a2) ,x))))
       ((eq? a2 x) (list (Instr 'subq `(,(select-atm a1) ,x))))
       (else (list (Instr 'movq `(,(select-atm a1) ,x))
                   (Instr 'subq `(,(select-atm a2) ,x)))))]
    [else (list (Instr 'movq `(,(select-atm e) ,x)))]))

(define (select-tail e)
  (match e
    [(Return e)
     (append (select-stmt (Reg 'rax) e)
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (match stmt
       [(Assign (Var x) e) (append (select-stmt (Var x) e) (select-tail tail))])]))

(define (select-instructions-labels lts info)
  (cond
    ((null? lts) '())
    (else (cons (cons (caar lts) (Block info (select-tail (cdar lts))))
                (select-instructions-labels (cdr lts) info)))))

(define (select-instructions p)
  (match p
    [(CProgram info lts) (X86Program info (select-instructions-labels lts info))]))

;; assign-homes : x86var -> x86var
(define (assign-arg e homes)
  (match e
    [(Var x) (dict-ref homes x)]
    [else e]))

(define (assign-instr e homes)
  (match e
    [(Instr instr `(,arg1 ,arg2)) (Instr instr `(,(assign-arg arg1 homes) ,(assign-arg arg2 homes)))]
    [(Instr instr `(,arg)) (Instr instr `(,(assign-arg arg homes)))]
    [else e]))

(define (assign-block e)
  (match e
    [(Block info instrs)
     (define stack/homes (local->home (dict-ref info 'locals-types) -8))
     (Block (dict-set info 'stack-space (car stack/homes))
            (for/list ([instr instrs])
              (assign-instr instr (cdr stack/homes))))]))

(define (local->home locals stack)
  (cond
    ((null? locals) (cons (+ (- stack) (remainder (- stack) 16)) '()))
    (else
     (define ret (local->home (cdr locals) (- stack 8)))
     (cons (car ret)
           (cons (cons (caar locals) (Deref 'rbp stack))
                 (cdr ret))))))

(define (assign-homes p)
  (match p
    [(X86Program info lbs) (X86Program info (for/list ([lb lbs]) (cons (car lb) (assign-block (cdr lb)))))]))

;; patch-instructions : x86var -> x86int

(define (administer-patch instr arg1 arg2)
  (list (Instr 'movq `(,arg1 ,(Reg 'rax)))
        (Instr instr `(,(Reg 'rax) ,arg2))))

(define (patch-instr e)
  (match e
    [(Instr instr `(,arg1 ,arg2))
     (match `(,arg1 ,arg2)
       [`(,(Deref reg1 int1) ,(Deref reg2 int2)) (administer-patch instr arg1 arg2)]
       [`(,(Imm int1) ,(Deref reg int2)) #:when (> int1 (expt 2 16)) (administer-patch instr arg1 arg2)]
       [`(,(Deref reg int1) ,(Imm int2)) #:when (> int2 (expt 2 16)) (administer-patch instr arg1 arg2)]
       [else (Instr instr `(,arg1 ,arg2))])]
    [else (list e)]))

(define (patch-block e)
  (match e
    [(Block info instrs) (Block info (flatten (for/list ([instr instrs]) (patch-instr instr))))]))

(define (patch-instructions p)
  (match p
    [(X86Program info bls) (X86Program info (for/list ([lb bls]) (cons (car lb) (patch-block (cdr lb)))))]))

;; prelude-and-conclusion : x86int -> x86int
(define (get-start-stack-size bls)
  (cond
    ((eq? (caar bls) 'start)
     (match-let ([(Block info instrs) (cdar bls)]) (dict-ref info 'stack-space)))
    (else (get-start-stack-size (cdr bls) '()))))

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info bls)
     (define stack-size (get-start-stack-size bls))
     (X86Program info
                 (append bls
                         (list
                          (cons 'main
                                (Block '()
                                       (list
                                        (Instr 'pushq `(,(Reg 'rbp)))
                                        (Instr 'movq `(,(Reg 'rsp) ,(Reg 'rbp)))
                                        (Instr 'subq `(,(Imm stack-size) ,(Reg 'rsp)))
                                        (Jmp 'start))))
                          (cons 'conclusion
                                (Block '()
                                       (list
                                        (Instr 'addq `(,(Imm stack-size) ,(Reg 'rsp)))
                                        (Instr 'popq `(,(Reg 'rbp)))
                                        (Retq)))))))]))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish
    ("partial evaluate", pe-Lint, interp-Lvar, type-check-Lvar)
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions , interp-x86-0)
    ("assign homes" ,assign-homes ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
