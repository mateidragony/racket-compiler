#lang racket
(require racket/set racket/stream)
(require racket/promise)
(require racket/fixnum)
(require graph)
(require "interp.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
;;(require "interp-Lvar.rkt")
;;(require "interp-Cvar.rkt")
;;(require "type-check-Lvar.rkt")
;;(require "type-check-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
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

(define (cmp? op)
  (or (equal? op 'eq?) (equal? op '<) (equal? op '<=) (equal? op '>) (equal? op '>=)))

(define (cmp->cmp-func cmp)
  (match cmp
    ['< <] ['> >] ['<= <=] ['>= >=] ['eq? eq?]))

(define (collapseable-let? e)
  (match e
    [(Int n) #t]
    [(Var x) #t]
    [(Bool b) #t]
    [else #f]))

(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [(Var x) (Prim '- (list (Var x)))]
    [(Prim 'read '()) (Prim '- (list (Prim 'read '())))]
    [(Prim '+ (list i1 i2)) (Prim '+ (list (pe-neg i1) (pe-neg i2)))]
    [(Let v r1 r2) (Let v r1 (pe-neg r2))]
    [(If e1 e2 e3) (If e1 (pe-neg e2) (pe-neg e3))]))

(define (pe-not r)
  (match r
    [(Bool b) (Bool (not b))]
    [(Var x) (Prim 'not (list (Var x)))]
    [(Prim '< (list e1 e2)) (Prim '>= (list e1 e2))]
    [(Prim '<= (list e1 e2)) (Prim '> (list e1 e2))]
    [(Prim '> (list e1 e2)) (Prim '<= (list e1 e2))]
    [(Prim '>= (list e1 e2)) (Prim '< (list e1 e2))]
    [(Prim 'eq? (list e1 e2)) (Prim 'not (list (Prim 'eq? (list e1 e2))))]
    [(Let v r1 r2) (Let v r1 (pe-not r2))]
    [(If e1 e2 e3) (If e1 (pe-not e2) (pe-not e3))]))

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

(define (pe-eq r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Bool (eq? n1 n2))]
    [((Var x1) (Var x2)) (if (eq? x1 x2) (Bool (eq? x1 x2)) (Prim 'eq? (list r1 r2)))]
    [((Bool b1) (Bool b2)) (Bool (eq? b1 b2))]
    [(_ _) (Prim 'eq? (list r1 r2))]))

(define (pe-if p t f)
  (match p
    [(Bool b) (if b t f)]
    [else (If p t f)]))

(define (pe-cmp cmp r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Bool ((cmp->cmp-func cmp) n1 n2))]
    [(_ _) (Prim cmp (list r1 r2))]))

(define (pe-exp e env)
  (match e
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Var x) (if (dict-has-key? env x)
                 (dict-ref env x)
                 (Var x))]
    [(If e1 e2 e3) (pe-if (pe-exp e1 env) (pe-exp e2 env) (pe-exp e3 env))]
    [(Let v e1 e2)
     (define val (pe-exp e1 env))
     (if (collapseable-let? val)
         (pe-exp e2 (dict-set env v val))
         (Let v val (pe-exp e2 (dict-remove env v))))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1 env))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1 env) (pe-neg (pe-exp e2 env)))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1 env) (pe-exp e2 env))]
    [(Prim 'eq? (list e1 e2)) (pe-eq (pe-exp e1 env) (pe-exp e2 env))]
    [(Prim cmp (list e1 e2)) #:when (cmp? cmp) (pe-cmp cmp (pe-exp e1 env) (pe-exp e2 env))]
    [(Prim 'not (list e1)) (pe-not (pe-exp e1 env))]))

(define (pe-Lif p)
  (match p
    [(Program info e) (Program info (pe-exp e '()))]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW3 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; shrink : Lif -> Lif
(define (shrink p)
  (match-let (((Program info e) p))
    (Program info (shrink-exp e))))

(define (shrink-exp e)
  (match e
    [(Prim 'and (list e1 e2)) (If e1 e2 (Bool #f))]
    [(Prim 'or (list e1 e2)) (If e1 (Bool #t) e2)]
    [(Prim op es) (Prim op (for/list [(e es)] (shrink-exp e)))]
    [(If e1 e2 e3) (If (shrink-exp e1) (shrink-exp e2) (shrink-exp e3))]
    [(Let v e1 e2) (Let v (shrink-exp e1) (shrink-exp e2))]
    [_ e]))

;; uniquify : Lif -> Lif
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
      [(Bool b) (Bool b)]
      [(Let x e body)
       (let ((new-name (uniquify-name x)))
         (Let new-name
              ((uniquify-exp env) e)
              ((uniquify-exp (dict-set env x new-name)) body)))]
      [(If e1 e2 e3) (If ((uniquify-exp env) e1) ((uniquify-exp env) e2) ((uniquify-exp env) e3))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))


(define (uniquify p)
  (begin
    (set! unique-number 0)
    (match p
      [(Program info e) (Program info ((uniquify-exp '()) e))])))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
      [(Program info e) (Program info (rco-exp e))]))

(define (atomize e)
  (define tmp (uniquify-name 'tmp))
  (cons (Var tmp) (dict-set '() tmp (rco-exp e))))

(define (rco-atom e)
  (match e
    [(Var x) (cons (Var x) '())]
    [(Int n) (cons (Int n) '())]
    [(Bool b) (cons (Bool b) '())]
    [(If e1 e2 e3) (atomize e)]
    [(Let x e^ body) (atomize e)]
    [(Prim op es) (atomize e)]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(If e1 e2 e3) (If (rco-exp e1) (rco-exp e2) (rco-exp e3))]
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
(define basic-blocks (make-hash))
(define (create-block tail)
  (delay
    (match (force tail)
      [(Goto label) (Goto label)]
      [else
       (define label (uniquify-name 'block))
       (dict-set! basic-blocks label (force tail))
       (Goto label)])))

(define (explicate-tail e)
  (delay
    (match e
      [(Var x) (Return (Var x))]
      [(Int n) (Return (Int n))]
      [(Bool b) (Return (Bool b))]
      [(If p bt bf) (explicate-pred p (explicate-tail bt) (explicate-tail bf))]
      [(Let x rhs body) (explicate-assign x rhs (explicate-tail body))]
      [(Prim op es) (Return (Prim op es))])))

(define (explicate-assign x e cont)
  (match e
    [(Var x^) (Seq (Assign (Var x) (Var x^)) (force cont))]
    [(Int n) (Seq (Assign (Var x) (Int n)) (force cont))]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) (force cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) (force cont))]
    [(If p bt bf)
     (define block (create-block cont))
     (explicate-pred p (delay (explicate-assign x bt block)) (delay (explicate-assign x bf block)))]
    [(Let y rhs body) (explicate-assign y rhs (explicate-assign x body cont))]))

(define (explicate-pred p bt bf)
  (match p
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (force (create-block bt)) (force (create-block bf)))]
    [(Bool b) (if b (force bt) (force bf))]
    [(Let x rhs body) (explicate-assign x rhs (explicate-pred body bt bf))]
    [(Prim 'not (list (Bool b))) (if (not b) (force bt) (force bf))]
    [(Prim op es) (IfStmt (Prim op es) (force (create-block bt)) (force (create-block bf)))]
    [(If p^ bt^ bf^)
     (define true-block (create-block bt))
     (define false-block (create-block bf))
     (explicate-pred p^
                     (delay (explicate-pred bt^ true-block false-block))
                     (delay (explicate-pred bf^ true-block false-block)))]))

(define (explicate-control p)
  (match-let (((Program info body) p))
    (set! basic-blocks (make-hash))
    (define start (force (explicate-tail body)))
    (CProgram info (cons `(start . ,start) (dict->list basic-blocks)))))

;; select-instructions : Cvar -> x86var
(define (select-atm e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [else (error "Not an atom")]))

(define (get-cc op)
  (match op
    ['eq? 'e]
    ['< 'l]
    ['<= 'le]
    ['> 'g]
    ['>= 'ge]))

(define (select-stmt x e)
  (match e
    [(Prim 'read '())
     (list (Callq 'read_int 0)
           (Instr 'movq (list (Reg 'rax) x)))]
    [(Prim '- (list a))
     (if (equal? a x)
         (list (Instr 'negq (list x)))
         (list (Instr 'movq (list (select-atm a) x))
               (Instr 'negq (list x))))]
    [(Prim '+ (list a1 a2))
     (cond
       ((equal? a1 x) (list (Instr 'addq (list (select-atm a2) x))))
       ((equal? a2 x) (list (Instr 'addq (list (select-atm a1) x))))
       (else (list (Instr 'movq (list (select-atm a1) x))
                   (Instr 'addq (list(select-atm a2) x)))))]
    [(Prim '- (list a1 a2))
     (cond
       ((equal? a1 x) (list (Instr 'subq (list (select-atm a2) x))))
       ((equal? a2 x) (list (Instr 'subq (list (select-atm a1) x))))
       (else (list (Instr 'movq (list (select-atm a1) x))
                   (Instr 'subq (list (select-atm a2) x)))))]
    [(Prim 'not (list e))
     (if (equal? e x)
         (list (Instr 'xorq (list (Imm 1) x)))
         (list (Instr 'movq (list (select-atm e) x))
               (Instr 'xorg (list (Imm 1) select-atm ))))]
    [(Prim op (list e1 e2))
     #:when (cmp? op)
     (list (Instr 'cmpq (list (select-atm e2) (select-atm e1)))
           (Instr 'set (list (get-cc op) (ByteReg 'al)))
           (Instr 'movzbq (list (ByteReg 'al) x)))]
    [else (list (Instr 'movq (list (select-atm e) x)))]))

(define (select-tail e)
  (match e
    [(Return e)
     (append (select-stmt (Reg 'rax) e)
             (list (Jmp 'conclusion)))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim cmp (list a1 a2)) (Goto lt) (Goto lf))
     (list (Instr 'cmpq (list (select-atm a2) (select-atm a1)))
           (JmpIf (get-cc cmp) lt)
           (Jmp lf))]
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


;; uncover-live : x86var -> x86var
(define caller-saved-registers '(rax rcx rdx rsi rdi r8 r9 r10 r11))
(define callee-saved-registers '(rsp rbp rbx r12 r13 r14 r15))

(define (get-live-after instrs lafter label->live)
  (match instrs
    [`() (cons lafter '())]
    [`(,instr . ,instrs)
     (define ret (get-live-after instrs lafter label->live))
     (define lbefore (get-lbefore instr (car ret) label->live))
     (cons lbefore
           ret)]))

(define (get-lbefore instr lafter label->live)
  (match instr
    [(Jmp label) (dict-ref label->live label)]
    [(JmpIf cc label) (set-union lafter (dict-ref label->live label))]
    [else (set-union (set-subtract lafter (locations-write instr)) (locations-read instr))]))

(define (locations-args arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    [(ByteReg r) (set (bytereg->reg r))] 
    [else (set)]))

(define (get-arg-regs-used arity args)
  (cond
    ((zero? arity) (set))
    ((null? args) (set))
    (else (set-union (set (car args))
                     (get-arg-regs-used (sub1 arity) (cdr args))))))

(define (locations-read instr)
  (match instr
    [(Instr 'movq (list a1 a2)) (locations-args a1)]
    [(Instr 'addq (list a1 a2)) (set-union (locations-args a1) (locations-args a2))]
    [(Instr 'subq (list a1 a2)) (set-union (locations-args a1) (locations-args a2))]
    [(Instr 'xorq (list a1 a2)) (set-union (locations-args a1) (locations-args a2))]
    [(Instr 'cmpq (list a1 a2)) (set-union (locations-args a1) (locations-args a2))]
    [(Instr 'movzbq (list a1 a2)) (set-union (locations-args a1) (locations-args a2))]
    [(Instr 'set (list cc a)) (locations-args a)]
    [(Instr 'negq (list a)) (locations-args a)]
    [(Instr 'pushq (list a)) (locations-args a)]
    [(Instr 'popq (list a)) (locations-args a)]
    [(Callq label arity) (get-arg-regs-used arity arg-registers)]
    [else (set)]))

(define (locations-write instr)
  (match instr
    [(Instr 'movq (list a1 a2)) (locations-args a2)]
    [(Instr 'addq (list a1 a2)) (locations-args a2)]
    [(Instr 'subq (list a1 a2)) (locations-args a2)]
    [(Instr 'xorq (list a1 a2)) (locations-args a2)]
    [(Instr 'set (list cc a2)) (locations-args a2)]
    [(Instr 'movzbq (list a1 a2)) (locations-args a2)]
    [(Instr 'negq (list a)) (locations-args a)]
    [else (set)]))

(define (uncover-block info instrs label->live)
  (define lafter (get-live-after instrs (set) label->live))
  (values
   lafter
   (Block (dict-set info 'live-after-sets lafter) instrs)))

(define (uncover-bls bls label->live)
  (cond
    ((null? bls) '())
    (else
     (match-let ([(cons label (Block info instrs)) (car bls)])
       (define-values (lafter b) (uncover-block info instrs label->live))
       (cons (cons label b)
             (uncover-bls (cdr bls) (cons (cons label (car lafter))
                                          label->live)))))))

(define (get-jmp-labels instrs)
  (cond
    ((null? instrs) (values '() '()))
    (else
     (define-values (jmp-labels jmpif-labels) (get-jmp-labels (cdr instrs)))
     (match (car instrs)
       [(Jmp label) (values (cons label jmp-labels) jmpif-labels)]
       [(JmpIf cc label) (values jmp-labels (cons label jmpif-labels))]
       [else (values jmp-labels jmpif-labels)]))))

(define (build-cf-graph cfg cfg-only-jmp bls)
  (cond
    ((null? bls) '())
    (else
     (match-let ([(cons label (Block info instrs)) (car bls)])
       (define-values (jmp-labels jmpif-labels) (get-jmp-labels instrs))
       (for ([jmp jmp-labels])   (add-directed-edge! cfg label jmp)
                                 (add-directed-edge! cfg-only-jmp label jmp))
       (for ([jmp jmpif-labels]) (add-directed-edge! cfg label jmp)))
     (build-cf-graph cfg cfg-only-jmp (cdr bls)))))

(define (uncover-live p)
  (match-let [((X86Program info bls) p)]
    (define cfg (make-multigraph '()))
    (define cfg-only-jmp (make-multigraph '()))
    (build-cf-graph cfg cfg-only-jmp bls)
    (define ordered-bls (map (λ (l) (cons l (dict-ref bls l)))
                             (remove 'conclusion (tsort (transpose cfg)))))
    (X86Program (dict-set (dict-set info 'cf-graph cfg) 'cf-graph-only-jmp cfg-only-jmp)
                (uncover-bls ordered-bls
                             (dict-set '() 'conclusion (set 'rax 'rsp))))))

;; build-interference : x86var -> x86var
(define (bytereg->reg r)
  (match r
    ['ah 'rax] ['al 'rax] ['bh 'rbx] ['bl 'rbx]
    ['ch 'rcx] ['cl 'rcx] ['dh 'rdx] ['dl 'rdx]))

(define (get-var arg)
  (match arg
    [(Var x) x]
    [(Reg x) x]
    [else #f]))

(define (init-graph ig vars)
  (map (λ (reg) (add-vertex! ig reg))
       (append caller-saved-registers callee-saved-registers vars)))

(define (build-interference-rec bls ig mg)
  (match bls
    ['() '()]
    [`(,(cons label block) . ,bls)
     (match-let [((Block info instrs) block)]
       (add-edges instrs (cdr (dict-ref info 'live-after-sets)) ig mg))
     (build-interference-rec bls ig mg)]))

(define (add-edges instrs live-after-sets ig mg)
  (cond
    [(null? live-after-sets) '()]
    [else
     (add-edge (car instrs) (car live-after-sets) ig mg)
     (add-edges (cdr instrs) (cdr live-after-sets) ig mg)]))

(define (get-move-interference ig live-after s dr)
  (map (λ (d) (map (λ (v) (add-edge! ig d v))
                   (set->list (set-subtract live-after
                                            (set-union (locations-args s) (set d))))))
       (set->list (locations-args dr))))

(define (add-edge instr live-after ig mg)
  (match instr
    [(Callq label int) (map (λ (d)
                              (map (λ (v) (add-edge! ig d v))
                                   (set->list live-after)))
                            caller-saved-registers)]
    [(Instr 'movq (list s dr))
     ;; move bias
     (if (and (get-var s) (get-var dr))
         (add-edge! mg (get-var s) (get-var dr))
         #f)
     ;; interference
     (get-move-interference ig live-after s dr)]
    [(Instr 'movzbq (list s dr)) (get-move-interference ig live-after s dr)]
    [else (map (λ (d)
                 (map (λ (v) (add-edge! ig d v))
                      (set->list (set-subtract live-after (set d)))))
               (set->list (locations-write instr)))]))

(define (build-interference p)
  (match-let [((X86Program info bls) p)]
    (define ig (undirected-graph '()))
    (define mg (undirected-graph '()))
    (init-graph ig '())
    (init-graph mg (map car (dict-ref info 'locals-types)))
    (build-interference-rec bls ig mg)
    (X86Program (dict-set (dict-set info 'move_graph mg) 'conflicts ig) bls)))

;; allocate-registers : x86var -> x86var

(define (reg->color reg)
  (match reg
    ['rcx 0] ['rdx 1] ['rsi 2] ['rdi 3] ['r8 4] ['r9 5] ['r10 6] ['rbx 7] ['r12 8] ['r13 9] ['r14 10]
    ['rax -1] ['rsp -2] ['rbp -3] ['r11 -4] ['r15 -5]))

(define (color->reg c)
  (match c
    [0 'rcx] [1 'rdx] [2 'rsi] [3 'rdi] [4 'r8] [5 'r9] [6 'r10] [7 'rbx] [8 'r12] [9 'r13] [10 'r14]
    [-1 'rax] [-2 'rsp] [-3 'rbp] [-4 'r11] [-5 'r15]))

(define (reg? reg)
  (match reg
    ['rcx #t] ['rdx #t] ['rsi #t] ['rdi #t] ['r8 #t] ['r9 #t] ['r10 #t] ['rbx #t] ['r12 #t]
    ['r13 #t] ['r14 #t] ['rax #t] ['rsp #t] ['rbp #t] ['r11 #t] ['r15 #t] [else #f]))

(define (init-color-list ig vs)
  (match vs
    [`() '()]
    [`(,v . ,vs) #:when (reg? v) (init-color-list ig vs)] ;; no need for pencil marks for registers
    [`(,v . ,vs) (cons (cons v (box (init-pencil-marks (sequence->list (in-neighbors ig v))))) (init-color-list ig vs))]))

(define (init-pencil-marks ns)
  (match ns
    [`() (set)]
    [`(,n . ,ns) #:when (reg? n) (set-union (set (reg->color n)) (init-pencil-marks ns))]
    [`(,n . ,ns) (init-pencil-marks ns)]))

(define (pq-insert-ls pq is)
  (match is
    ['() '()]
    [`(,i . ,is) (dict-set (pq-insert-ls pq is) (car i) (pqueue-push! pq i))]))

(define (assign-color-mb v sat mg)
  (define all-move-related-colors (set->list (get-move-related-colors mg v sat)))
  (define move-related-colors (filter (λ (v) (<= v 10)) all-move-related-colors)) ;; ensure it is still a register
  (define assigned-color (assign-color 0 sat))
  (cond
    ((not (null? move-related-colors)) (car move-related-colors))         ;; move related register
    ((< 11 assigned-color) assigned-color)                                ;; non move related register
    ((not (null? all-move-related-colors)) (car all-move-related-colors)) ;; move related stack position
    (else assigned-color)))                                               ;; non move related stack position

(define (assign-color cur sat)
  (if (not (set-member? sat cur))
      cur
      (assign-color (add1 cur) sat)))

(define (update-pq pq neighbors c box-list handles)
  (match neighbors
    ['() '()]
    [`(,n . ,neighbors) #:when (dict-has-key? box-list n)
     (define sat-box (dict-ref box-list n))
     (set-box! sat-box (set-union (set c) (unbox sat-box)))
     (pqueue-decrease-key! pq (dict-ref handles n))
     (update-pq pq neighbors c box-list handles)]
    [`(,n . ,neighbors) (update-pq pq neighbors c box-list handles)]))

(define (dsatur pq ig box-list handles mg)
  (cond
    [(zero? (pqueue-count pq)) '()]
    [else
     (define v (pqueue-pop! pq))
     (define c (assign-color-mb (car v) (unbox (cdr v)) mg))
     (rename-vertex! mg (car v) (cons (car v) c))
     (update-pq pq (sequence->list (in-neighbors ig (car v))) c box-list handles)
     (cons (cons (car v) c)
           (dsatur pq ig box-list handles mg))]))

(define (get-move-related-colors mg v sat)
  (filter (λ (v) (not (set-member? sat v))) (map cdr (filter pair? (sequence->list (in-neighbors mg v))))))

(define (color-graph ig vars mg)
  (define pq (make-pqueue (λ (a b) (if (equal? (set-count (unbox (cdr a))) (set-count (unbox (cdr b))))
                                       ;; check for move related variables and see if color is available
                                       (> (length (get-move-related-colors mg (car a) (unbox (cdr a))))
                                          (length (get-move-related-colors mg (car b) (unbox (cdr b)))))
                                       ;; else max pq by saturation
                                       (> (set-count (unbox (cdr a))) (set-count (unbox (cdr b))))))))
  (define box-list (init-color-list ig vars))
  (define handles (pq-insert-ls pq box-list))
  (dsatur pq ig box-list handles mg))

(define (color->home c)
  (if (<= c 10)
      (Reg (color->reg c))
      (Deref 'rbp (* -8 (- c 10)))))

(define (colors->homes cs) ;; callees , spilled , homes
  (match cs
    ['() (values (set) 0 '())]
    [`(,c . ,cs)
     (define home (color->home (cdr c)))
     (define-values (callees spilled homes) (colors->homes cs))
     (match home
       [(Reg r) (values (if (member r callee-saved-registers)
                          (set-union (set home) callees)
                          callees)
                        spilled
                        (cons (cons (car c) home) homes))]
       [(Deref 'rbp n) (values callees
                               (add1 spilled)
                               (cons (cons (car c) home) homes))])]))

(define (assign-arg e homes)
  (match e
    [(Var x) (dict-ref homes x)]
    [else e]))

(define (assign-instr e homes)
  (match e
    [(Instr instr `(,arg1 ,arg2)) (Instr instr `(,(assign-arg arg1 homes) ,(assign-arg arg2 homes)))]
    [(Instr instr `(,arg)) (Instr instr `(,(assign-arg arg homes)))]
    [else e]))

(define (assign-block e homes)
  (match e
    [(Block info instrs)
     (Block info (for/list ([instr instrs]) (assign-instr instr homes)))]))

(define (allocate-registers p)
  (match-let [((X86Program info bls) p)]
    (define-values (callees spilled homes)
      (colors->homes (color-graph (dict-ref info 'conflicts)
                                  (map car (dict-ref info 'locals-types))
                                  (dict-ref info 'move_graph))))
    (X86Program (dict-set (dict-set info 'num_spilled spilled)
                          'used_callee callees)
                (for/list ([bl bls]) (cons (car bl) (assign-block (cdr bl) homes))))))

;; remove-jumps

(define (concat-bls bls concat removed)
  (match-let ([(Block c-info c-instrs) (dict-ref bls concat)]
              [(Block r-info r-instrs) (dict-ref bls removed)])
    (Block c-info (append (drop-right c-instrs 1) ;; drop the jmp
                          r-instrs))))

(define (remove-jumps-bls bls removable)
  (cond
    ((null? removable) bls)
    (else (remove-jumps-bls (dict-set bls (cdar removable)
                                      (concat-bls bls (cdar removable) (caar removable)))
                            (cdr removable)))))
  
(define (remove-jumps p)
  (match-let [((X86Program info bls) p)]
    (define cfgoj (transpose (dict-ref info 'cf-graph-only-jmp)))
    (define removable (filter-map (λ (e)
                                    (if (and (equal? 1 (length (in-neighbors cfgoj e)))
                                             (not (equal? e 'conclusion)))
                                        (cons e (car (in-neighbors cfgoj e)))
                                        #f))
                                  (tsort cfgoj)))
    (X86Program info (filter (λ (bl) (not (dict-has-key? removable (car bl))))
                             (remove-jumps-bls bls removable)))))

;; patch-instructions : x86if -> x86if

(define (administer-patch-arg1 instr arg1 arg2)
  (list (Instr 'movq (list arg1 (Reg 'rax)))
        (Instr instr (list (Reg 'rax) arg2))))

(define (administer-patch-arg2 instr arg1 arg2)
  (list (Instr 'movq (list arg2 (Reg 'rax)))
        (Instr instr (list arg1 (Reg 'rax)))))

(define (patch-instr e)
  (match e
    [(Instr 'movq (list arg1 arg2)) #:when (equal? arg1 arg2) '()]
    [(Instr 'cmpq (list a1 (Imm n))) (administer-patch-arg2 'cmpq a1 (Imm n))]
    [(Instr 'movzbq (list a1 (Deref reg int))) (administer-patch-arg2 'movzbq a1 (Deref reg int))]
    [(Instr instr (list arg1 arg2))
     (match (list arg1 arg2)
       [(list (Deref reg1 int1) (Deref reg2 int2)) (administer-patch-arg1 instr arg1 arg2)]
       [(list (Imm int1) (Deref reg int2)) #:when (> int1 (expt 2 16)) (administer-patch-arg1 instr arg1 arg2)]
       [(list (Deref reg int1) (Imm int2)) #:when (> int2 (expt 2 16)) (administer-patch-arg1 instr arg1 arg2)]
       [else (Instr instr (list arg1 arg2))])]
    [else (list e)]))

(define (block-killable? instrs)
  (and (equal? 1 (length instrs))
       (match (car instrs)
         [(Jmp label) label]
         [else #f])))

(define (patch-block e)
  (match-let [((Block info instrs) e)]
    (define new-instrs (flatten (for/list ([instr instrs]) (patch-instr instr))))
    (values (Block info new-instrs) (block-killable? new-instrs))))

(define (patch-instructions p)
  (match-let [((X86Program info bls) p)]
    (define blocks/kills (for/list ([lb bls])
                           (define-values (block killable) (patch-block (cdr lb)))
                           (cons
                            (cons (car lb) block)
                            (if killable (cons (car lb) killable) '()))))
    (X86Program (dict-set info 'killable-blocks (filter (λ (ls) (not (null? ls)))
                                                        (map cdr blocks/kills))) (map car blocks/kills))))


;; kill-unused-blocks : x86if -> x86if (remove blocks that only contain a jump (arises from deleting movqs in patch-instructions))

(define (replace-jmps-instr instr killables)
  (match instr
    [(Jmp label) (if (dict-has-key? killables label)
                     (Jmp (dict-ref killables label))
                     (Jmp label))]
    [(JmpIf cc label) (if (dict-has-key? killables label)
                          (JmpIf cc (dict-ref killables label))
                          (JmpIf cc label))]
    [else instr]))

(define (replace-jmps instrs killables)
  (if (null? instrs)
      '()
      (cons (replace-jmps-instr (car instrs) killables)
            (replace-jmps (cdr instrs) killables))))

(define (replace-jmps-bls bls killables)
  (match bls
    ['() '()]
    [(cons (cons label (Block info instrs)) bls)
     (cons (cons label (Block info (replace-jmps instrs killables)))
           (replace-jmps-bls bls killables))]))

(define (kill-unused-blocks p)
  (match-let ([(X86Program info bls) p])
    (define killables (dict-ref info 'killable-blocks))
    (X86Program info (filter (λ (bl) (not (dict-has-key? killables (car bl))))
                             (replace-jmps-bls bls killables)))))

;; prelude-and-conclusion : x86if -> x86if

(define (prelude-and-conclusion p)
  (match-let [((X86Program info bls) p)]
    (define spilled (dict-ref info 'num_spilled))
    (define callee (dict-ref info 'used_callee))
    (define stack-size (- (align (+ (* 8 spilled) (* 8 (set-count callee))) 16) (* 8 (set-count callee))))
    (X86Program info
                (append bls
                        (list
                         (cons 'main
                               (Block '()
                                      (flatten
                                       (list
                                        (Instr 'pushq `(,(Reg 'rbp)))
                                        (Instr 'movq `(,(Reg 'rsp) ,(Reg 'rbp)))
                                        (for/list [(cr (set->list callee))] (Instr 'pushq `(,cr)))
                                        (Instr 'subq `(,(Imm stack-size) ,(Reg 'rsp)))
                                        (Jmp 'start)))))
                         (cons 'conclusion
                               (Block '()
                                      (flatten
                                       (list
                                        (Instr 'addq `(,(Imm stack-size) ,(Reg 'rsp)))
                                        (for/list [(cr (reverse (set->list callee)))] (Instr 'popq `(,cr)))
                                        (Instr 'popq `(,(Reg 'rbp)))
                                        (Retq))))))))))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ;; Uncomment the following passes as you finish
    ("shrink", shrink, interp-Lif, type-check-Lif)
    ("partial evaluate", pe-Lif, interp-Lif, type-check-Lif)
    ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
    ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
    ("instruction selection" ,select-instructions , interp-x86-1)
    ("uncover live", uncover-live, interp-x86-1)
    ("build interference", build-interference, interp-x86-1)
    ("allocate registers", allocate-registers, interp-x86-1)
    ("remove jumps", remove-jumps, interp-x86-1)
    ("patch instructions" ,patch-instructions ,interp-x86-1)
    ("kill unused blocks", kill-unused-blocks, interp-x86-1)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
    ))
