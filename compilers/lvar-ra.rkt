#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "../interp-Lint.rkt")
(require "../interp-Lvar.rkt")
(require "../interp-Cvar.rkt")
(require "../type-check-Lvar.rkt")
(require "../interp.rkt")
(require "../type-check-Cvar.rkt")
(require "../utilities.rkt")
(require "../priority_queue.rkt")
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
;; HW2 Passes
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


;; uncover-live : x86var -> x86var
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
    [else (set-union (set-subtract lafter (locations-write instr)) (locations-read instr))]))

(define (locations-args arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    [else (set)]))

(define (locations-read instr)
  (match instr
    [(Instr 'movq (list a1 a2)) (locations-args a1)]
    [(Instr 'addq (list a1 a2)) (set-union (locations-args a1) (locations-args a2))]
    [(Instr 'subq (list a1 a2)) (set-union (locations-args a1) (locations-args a2))]
    [(Instr 'negq (list a)) (locations-args a)]
    [(Instr 'pushq (list a)) (locations-args a)]
    [(Instr 'popq (list a)) (locations-args a)]
    [else (set)]))

(define (locations-write instr)
  (match instr
    [(Instr 'movq (list a1 a2)) (locations-args a2)]
    [(Instr 'addq (list a1 a2)) (locations-args a2)]
    [(Instr 'subq (list a1 a2)) (locations-args a2)]
    [(Instr 'negq (list a)) (locations-args a)]
    [else (set)]))

(define (uncover-live p)
  (match-let [((X86Program info bls) p)]
    (X86Program info (for/list [(bl bls)]
                       (match-let ([(cons label (Block info instrs)) bl])
                         (cons label (Block (dict-set info
                                          'live-after-sets
                                          (get-live-after instrs (set) (dict-set '() 'conclusion (set 'rax 'rsp))))
                                instrs)))))))

;; build-interference : x86var -> x86var
(define caller-saved-registers '(rax rcx rdx rsi rdi r8 r9 r10 r11))
(define callee-saved-registers '(rsp rbp rbx r12 r13 r14 r15))

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
     (map (λ (d) (map (λ (v) (add-edge! ig d v))
                      (set->list (set-subtract live-after
                                               (set-union (locations-args s) (set d))))))
          (set->list (locations-args dr)))]
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
  (define move-related-colors (filter (λ (v) (<= v 10)) ;; ensure it is still a register
                                      (set->list (get-move-related-colors mg v sat))))
  (if (not (null? move-related-colors))
      (car move-related-colors)
      (assign-color 0 sat)))

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

;; patch-instructions : x86var -> x86int

(define (administer-patch instr arg1 arg2)
  (list (Instr 'movq `(,arg1 ,(Reg 'rax)))
        (Instr instr `(,(Reg 'rax) ,arg2))))

(define (patch-instr e)
  (match e
    [(Instr 'movq `(,arg1 ,arg2)) #:when (equal? arg1 arg2) '()]
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
;; save and restore callee registers

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info bls)
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
                                         (Retq))))))))]))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
     ;; Uncomment the following passes as you finish
    ;;("partial evaluate", pe-Lint, interp-Lvar, type-check-Lvar)
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions , interp-x86-0)
    ("uncover live", uncover-live, interp-x86-0)
    ("build interference", build-interference, interp-x86-0)
    ("allocate registers", allocate-registers, interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
