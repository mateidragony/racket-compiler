#lang racket
(require racket/set racket/stream)
(require racket/promise)
(require racket/fixnum)
(require graph)
(require data/queue)
(require "interp.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cwhile.rkt")
(provide (all-defined-out))

;; Shulin Calvin and I discuss our solutions
;; but we each work independently and have our
;; own personal solutions

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; shrink : Lwhile -> Lwhile
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    [(SetBang v e) (SetBang v (shrink-exp e))]
    [(Begin es ef) (Begin (for/list ([e es]) (shrink-exp e)) (shrink-exp ef))]
    [(WhileLoop c b) (WhileLoop (shrink-exp c) (shrink-exp b))]
    [_ e]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uniquify : Lwhile -> Lwhile
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(SetBang v e) (SetBang (dict-ref env v) ((uniquify-exp env) e))]
      [(Begin es ef)
       (Begin (for/list ([e es]) ((uniquify-exp env) e)) ((uniquify-exp env) ef))]
      [(WhileLoop c b) (WhileLoop ((uniquify-exp env) c) ((uniquify-exp env) b))]
      [(Void) (Void)])))


(define (uniquify p)
  (begin
    (set! unique-number 0)
    (match p
      [(Program info e) (Program info ((uniquify-exp '()) e))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover-get! : Lwhile -> Lwhile
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (collect-set! e)
  (match e
    [(Prim op es) (for/fold ([set-union (set)]) ([e es]) (collect-set! e))]
    [(If e1 e2 e3) (set-union (collect-set! e1) (collect-set! e2) (collect-set! e3))]
    [(Let v e1 e2) (set-union (collect-set! e1) (collect-set! e2))]
    [(SetBang v e) (set-union (set v) (collect-set! e))]
    [(Begin es ef) (set-union (for/fold ([set-union (set)]) ([e es]) (collect-set! e)) (collect-set! ef))]
    [(WhileLoop c b) (set-union (collect-set! c) (collect-set! b))]
    [_ (set)]))

(define (uncover-get!-expr set!-vars e)
  (match e
    [(Var x) (if (set-member? set!-vars x)
                 (GetBang x)
                 (Var x))]
    [(Prim op es) (Prim op (for/list [(e es)] (uncover-get!-expr set!-vars e)))]
    [(If e1 e2 e3) (If (uncover-get!-expr set!-vars e1)
                       (uncover-get!-expr set!-vars e2)
                       (uncover-get!-expr set!-vars e3))]
    [(Let v e1 e2) (Let v (uncover-get!-expr set!-vars e1) (uncover-get!-expr set!-vars e2))]
    [(SetBang v e) (SetBang v (uncover-get!-expr set!-vars e))]
    [(Begin es ef) (Begin (for/list ([e es]) (uncover-get!-expr set!-vars e)) (uncover-get!-expr set!-vars ef))]
    [(WhileLoop c b) (WhileLoop (uncover-get!-expr set!-vars c) (uncover-get!-expr set!-vars b))]
    [_ e]))

(define (uncover-get! e)
  (match-let [((Program info e) e)]
    (Program info (uncover-get!-expr (collect-set! e) e))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remove-complex-opera* : Lwhile -> Lwhile^mon
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    [(Void) (cons (Void) '())]
    [_ (atomize e)]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(If e1 e2 e3) (If (rco-exp e1) (rco-exp e2) (rco-exp e3))]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es) (primops->letexp es op '())]
    [(GetBang v) (GetBang v)]
    [(SetBang v e) (SetBang v (rco-exp e))]
    [(Begin es ef) (Begin (for/list [(e es)] (rco-exp e)) (rco-exp ef))]
    [(WhileLoop c b) (WhileLoop (rco-exp c) (rco-exp b))]))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; explicate-control : Lwhile^mon -> Cwhile
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define basic-blocks (make-hash))
(define (create-block tail)
  (delay
    (match (force tail)
      [(Goto label) (Goto label)]
      [else
       (define label (uniquify-name 'block))
       (dict-set! basic-blocks label (force tail))
       (Goto label)])))

(define (explicate-loop c b cont)
  (define loop (uniquify-name 'loop))
  (define body (explicate-effect b (Goto loop)))
  (define cnd  (explicate-pred c body cont))
  (dict-set! basic-blocks loop cnd)
  (Goto loop))


(define (explicate-tail e)
  (delay
    (match e
      [(Var x) (Return (Var x))]
      [(GetBang x) (Return (Var x))]
      [(Int n) (Return (Int n))]
      [(Bool b) (Return (Bool b))]
      [(Void) (Return (Void))]
      [(If p bt bf) (explicate-pred p (explicate-tail bt) (explicate-tail bf))]
      [(Let x rhs body) (explicate-assign x rhs (explicate-tail body))]
      [(Prim op es) (Return (Prim op es))]
      [(WhileLoop c b) (explicate-loop c b (Return (Void)))]
      [(SetBang v e) (explicate-assign v e)]
      [(Begin es ef) (foldr explicate-effect (explicate-tail ef) es)])))

(define (explicate-assign x e cont)
  (match e
    [(Var x^) (Seq (Assign (Var x) (Var x^)) (force cont))]
    [(GetBang x^) (Seq (Assign (Var x) (Var x^)) (force cont))]
    [(Int n) (Seq (Assign (Var x) (Int n)) (force cont))]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) (force cont))]
    [(Void) (Seq (Assign (Var x) (Void)) (force cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) (force cont))]
    [(If p bt bf)
     (define block (create-block cont))
     (explicate-pred p (delay (explicate-assign x bt block)) (delay (explicate-assign x bf block)))]
    [(Let y rhs body) (explicate-assign y rhs (explicate-assign x body cont))]
    [(WhileLoop c b) (explicate-loop c b (Seq (Assign (Var x) (Void)) (force cont)))]
    [(SetBang v e) (Seq (explicate-assign v e) (Seq (Assign (Var x) (Void)) (force cont)))]
    [(Begin es ef) (foldr explicate-effect (explicate-assign x ef cont) es)]))

(define (explicate-pred p bt bf)
  (match p
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (force (create-block bt)) (force (create-block bf)))]
    [(GetBang x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (force (create-block bt)) (force (create-block bf)))]
    [(Bool b) (if b (force bt) (force bf))]
    [(Let x rhs body) (explicate-assign x rhs (explicate-pred body bt bf))]
    [(Prim 'not (list (Bool b))) (if (not b) (force bt) (force bf))]
    [(Prim op es) (IfStmt (Prim op es) (force (create-block bt)) (force (create-block bf)))]
    [(If p^ bt^ bf^)
     (define true-block (create-block bt))
     (define false-block (create-block bf))
     (explicate-pred p^
                     (delay (explicate-pred bt^ true-block false-block))
                     (delay (explicate-pred bf^ true-block false-block)))]
    [(Begin es ef) (foldr explicate-effect (explicate-pred ef bt bf) es)]))

(define (combine-side-effects se)
  (cons (foldr (λ (a b) (or (car a) b)) #f se)
        se))

(define (get-side-effect e)
  (match e
    [(SetBang v e) (cons #t (list #t))]
    [(Prim 'read '()) (cons #t (list #t))]
    [(Prim op es) (combine-side-effects (map get-side-effect es))]
    [(Let v e1 e2) (combine-side-effects (list (get-side-effect e1) (get-side-effect e2)))]
    [(If p bt bf) (combine-side-effects (list (get-side-effect p) (get-side-effect bt) (get-side-effect bf)))]
    [(WhileLoop c b) (combine-side-effects (list (get-side-effect c) (get-side-effect b)))]
    [(Begin es ef) (combine-side-effects (append (map get-side-effect es) (list (get-side-effect ef))))]
    [_ (cons #f (list #f))]))

(define (explicate-effect e cont [se #f])
  (define side-effects (if se se (get-side-effect e)))
  (if (not (car side-effects)) ;; no side effects anywhere
      cont
      (match e
        [(Prim 'read '()) (Seq (Prim 'read '()) (force cont))]
        [(If p bt bf)
         (if (and (car (first (cdr side-effects))) ;; only predicate has side effect
                  (not (or (car (second (cdr side-effects))) (car (third (cdr side-effects)))))) 
             (explicate-effect p cont (first (cdr side-effects)))
             (let ((block (create-block cont)))
               (explicate-pred p (delay (explicate-effect bt cont (second (cdr side-effects))))
                               (delay (explicate-effect bf cont (third (cdr side-effects)))))))]
        [(Let x rhs body)
         (if (and (car (first (cdr side-effects))) (not (car (second (cdr side-effects)))))
             (explicate-effect rhs cont (first (cdr side-effects)))
             (explicate-assign x rhs (explicate-effect body cont (second (cdr side-effects)))))]
        [(WhileLoop c b) (explicate-loop c b cont)]
        [(SetBang v e) (explicate-assign v e cont)]
        [(Begin es ef)
         (foldr (λ (e/s c) (explicate-effect (car e/s) c (cdr e/s))) cont
                (filter-map (λ (e se) (and (car se) (cons e se))) (append es (list ef)) (cdr side-effects)))]
        [_ cont])))

(define (explicate-control p)
  (match-let (((Program info body) p))
    (set! basic-blocks (make-hash))
    (define start (force (explicate-tail body)))
    (CProgram info (cons `(start . ,start) (dict->list basic-blocks)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; select-instructions : Cwhile -> x86while
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (select-atm e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(Void) (Imm 0)]
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
       [(Assign (Var x) e) (append (select-stmt (Var x) e) (select-tail tail))]
       [(Prim 'read '()) (cons (Callq 'read_int 0) (select-tail tail))])]))

(define (select-instructions-labels lts info)
  (cond
    ((null? lts) '())
    (else (cons (cons (caar lts) (Block info (select-tail (cdar lts))))
                (select-instructions-labels (cdr lts) info)))))

(define (select-instructions p)
  (match p
    [(CProgram info lts) (X86Program (dict-set info 'num-root-spills 0) (select-instructions-labels lts info))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; constant-propogation : x86while -> x86while
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (propogate? instr env)
  (or (and (dict-has-key? env instr) (dict-ref env instr))
      (match instr
        [(Imm i) #t]
        [else #f])))

(define (propogate-to? instr)
  (match instr
    [(Var x) #t]
    [else #f]))

(define (get-imm instr env)
  (match instr
    [(Imm i) i]
    [else (dict-ref env instr)]))

(define (propogate-tuah a1 a2 func rfunc env instr)
  (if (propogate? a1 env)
      (cond
        ((propogate? a2 env)
         (define new-imm (rfunc (get-imm a2 env) (get-imm a1 env)))
         (values (Instr 'movq (list (Imm new-imm) a2))
                 (dict-set env a2 new-imm)))
        (else (values (Instr func (list (Imm (get-imm a1 env)) a2)) env)))
      (if (propogate-to? a2)
          (values (Instr func (list a1 a2)) (dict-set env a2 #f))
          (values (Instr func (list a1 a2)) env))))

(define (propogate-instr instr env) ;; instr, new env
  (match instr
    [(Var x) #:when (propogate? instr env) (values (Imm (get-imm instr env)) env)]
    [(Instr 'movq (list s d)) (if (propogate? s env)
                                  (if (propogate-to? d)
                                      (values (Instr 'movq (list (Imm (get-imm s env)) d))
                                              (dict-set env d (get-imm s env)))
                                      (values (Instr 'movq (list (Imm (get-imm s env)) d)) env))
                                  (if (propogate-to? d)
                                      (values instr (dict-set env d #f))
                                      (values instr env)))]
    [(Instr 'addq (list a1 a2)) (propogate-tuah a1 a2 'addq + env instr)]
    [(Instr 'subq (list a1 a2)) (propogate-tuah a1 a2 'subq - env instr)]
    [(Instr 'xorq (list a1 a2)) (propogate-tuah a1 a2 'xorq bitwise-xor env instr)]
    [(Instr 'negq (list a)) (if (propogate? a env)
                                (values (Instr 'movq (list (Imm (- (get-imm a env))) a))
                                        (dict-set env a (- (get-imm a env))))
                                (if (propogate-to? a)
                                    (values instr (dict-set env a #f))
                                    (values instr env)))]
    [(Instr 'cmpq (list a1 a2))
     (cond ((and (propogate? a1 env) (propogate? a2 env))
            (values (Instr 'cmpq (list (Imm (get-imm a1 env)) (Imm (get-imm a2 env)))) env))
           ((propogate? a1 env) (values (Instr 'cmpq (list (Imm (get-imm a1 env)) a2)) env))
           ((propogate? a2 env) (values (Instr 'cmpq (list a1 (Imm (get-imm a2 env)))) env))
           (else (values instr env)))]
    [else (values instr env)]))

(define (propogate-block instrs env) ;; instrs, new env
  (match instrs
    ['() (values '() env)]
    [(cons instr instrs)
     (define-values (instr^ env^) (propogate-instr instr env))
     (define-values (instrs^ env^^) (propogate-block instrs env^))
     (values (if (null? instr^) instrs^ (cons instr^ instrs^)) env^^)]))

(define (var<? v1 v2)
  (match-let [((Var x1) v1)
              ((Var x2) v2)]
    (symbol<? x1 x2)))

(define (cp-transfer bls)
  (λ (label pre-env)
    (if (equal? label 'conclusion)
        pre-env
        (match-let [((Block info instrs) (dict-ref bls label))]
          (printf "label: ~a\n" label)
          (printf "Pre-env ~a\n" pre-env)
          (define-values (instrs^ env) (propogate-block instrs pre-env))
          (printf "New-env ~a\n\n" env)
          (dict-set! bls label (Block info instrs^))
          (sort env (λ (a1 a2) (var<? (car a1) (car a2))))))))

(define (cp-union env1 env2)
  (cond
    ((dict-empty? env1) env2)
    ((not (dict-has-key? env2 (caar env1))) (dict-set (cp-union (cdr env1) env2) (caar env1) (cdar env1)))
    ((eq? (cdar env1) (dict-ref env2 (caar env1))) (dict-set (cp-union (cdr env1) env2) (caar env1) (cdar env1)))
    (else (dict-set (cp-union (cdr env1) (dict-remove env2 (caar env1))) (caar env1) #f))))

(define (constant-propogation p)
  (match-let [((X86Program info bls) p)]
    (define mutable-bls (dict->mutable bls))
    (define cfg (make-multigraph '()))
    (define cfg-only-jmp (make-multigraph '()))
    (build-cf-graph cfg cfg-only-jmp bls)
    (add-vertex! cfg 'conclusion)
    (define df-analysis (analyze_dataflow cfg (cp-transfer mutable-bls) '() cp-union))
    (X86Program (dict-set (dict-set info 'cf-graph cfg) 'cf-graph-only-jmp cfg-only-jmp)
                (dict->list mutable-bls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover-live : x86while -> x86while
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define caller-saved-registers '(rax rcx rdx rsi rdi r8 r9 r10 r11))
(define callee-saved-registers '(rsp rbp rbx r12 r13 r14 r15))

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

(define (uncover-block info instrs label->live)
  (define lafter (get-live-after instrs (set) label->live))
  (values
   lafter
   (Block (dict-set info 'live-after-sets lafter) instrs)))

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

(define (get-label->live bls)
  (dict-set
   (for/list ([bl (dict->list bls)])
     (match-let [((cons label (Block info instrs)) bl)]
       (cons label (if (dict-has-key? info 'live-after-sets)
                       (first (dict-ref info 'live-after-sets))
                       (set)))))
   'conclusion (set 'rax 'rsp)))

(define (analyze-dataflow-transfer bls)
  (λ (label lafter)
    (if (equal? label 'conclusion)
        (set 'rax 'rsp)
        (match-let [((Block info instrs) (dict-ref bls label))]
          (define-values (lafters block) (uncover-block info instrs (get-label->live bls)))
          (dict-set! bls label block)
          (first lafters)))))

;; Thank you Siek <3
(define (analyze_dataflow G transfer bottom join)
  (define mapping (make-hash))
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
    (define node (dequeue! worklist))
    (define input (for/fold ([state bottom])
                            ([pred (in-neighbors trans-G node)])
                    (join state (dict-ref mapping pred))))
    (define output (transfer node input))
    (cond [(not (equal? output (dict-ref mapping node)))
          (dict-set! mapping node output)
          (for ([v (in-neighbors G node)])
            (enqueue! worklist v))]))
  mapping)

(define (dict->mutable d)
  (define d^ (make-hash))
  (dict-for-each d (λ (k v) (dict-set! d^ k v)))
  d^)

(define (uncover-live p)
  (match-let [((X86Program info bls) p)]
    (define mutable-bls (dict->mutable bls))
    (define df-analysis (analyze_dataflow (transpose (dict-ref info 'cf-graph)) (analyze-dataflow-transfer mutable-bls) (set) set-union))
    (X86Program info (dict->list mutable-bls))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eliminate-movqs : x86while -> x86while
;; - constant propogation coverts many instructions into movqs that sometimes become redundant. this pass removes those
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (get-symbol instr)
  (match instr
    [(Reg r) r]
    [(Var x) x]
    [else #f]))

(define (remove-movq? instr lafter)
  (match instr
    [(Instr 'movq (list s d)) #:when (not (set-member? lafter (get-symbol d))) #t]
    [else #f]))

(define (eliminate-movqs-instrs instrs lafters) ;; new instrs, new lafters
  (match* (instrs lafters)
    [('() '()) (values '() '())]
    [((cons instr instrs) (cons lafter lafters))
     (define-values (instrs^ lafters^) (eliminate-movqs-instrs instrs lafters))
     (if (remove-movq? instr lafter)
         (values instrs^ lafters^)
         (values (cons instr instrs^) (cons lafter lafters^)))])) 

(define (eliminate-movqs-block b)
  (match-let [((Block info instrs) b)]
    (define-values (instrs^ lafters^) (eliminate-movqs-instrs instrs (cdr (dict-ref info 'live-after-sets))))
    (Block (dict-set info 'live-after-sets (cons (car (dict-ref info 'live-after-sets))
                                                 lafters^)) instrs^)))

(define (eliminate-movqs p)
  (match-let [((X86Program info bls) p)]
    (X86Program info (for/list [(bl bls)] (cons (car bl) (eliminate-movqs-block (cdr bl)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; build-interference : x86while -> x86while
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    (init-graph ig (map car (dict-ref info 'locals-types)))
    (init-graph mg (map car (dict-ref info 'locals-types)))
    (build-interference-rec bls ig mg)
    (X86Program (dict-set (dict-set info 'move_graph mg) 'conflicts ig) bls)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; allocate-registers : x86while -> x86while
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    [`(,v . ,vs) #:when (has-vertex? ig v)
                 (cons (cons v (box (init-pencil-marks (sequence->list (in-neighbors ig v))))) (init-color-list ig vs))]
    [`(,v . ,vs) (init-color-list ig vs)]))

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
    [(Instr instr (list arg1 arg2)) (Instr instr (list (assign-arg arg1 homes) (assign-arg arg2 homes)))]
    [(Instr instr (list arg)) (Instr instr (list (assign-arg arg homes)))]
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remove-jumps
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; patch-instructions : x86while -> x86while
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; kill-unused-blocks : x86while -> x86while
;; - remove blocks that only contain a jump (arises from deleting movqs in patch-instructions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; prelude-and-conclusion : x86while -> x86while
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    ("shrink", shrink, interp-Lwhile, type-check-Lwhile)
    ;;("partial evaluate", pe-Lwhile, interp-Lwhile, type-check-Lwhile)
    ("uniquify" ,uniquify ,interp-Lwhile ,type-check-Lwhile)
    ("uncover-get!", uncover-get!, interp-Lwhile, type-check-Lwhile)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lwhile ,type-check-Lwhile)
    ("explicate control" ,explicate-control ,interp-Cwhile ,type-check-Cwhile)
    ("instruction selection" ,select-instructions , interp-x86-2)
    ("constant propogation", constant-propogation, interp-x86-2)    
    ("uncover live", uncover-live, interp-x86-2)
    ("eliminate movqs", eliminate-movqs, interp-x86-2)    
    ("build interference", build-interference, interp-x86-2)
    ("allocate registers", allocate-registers, interp-x86-2)
    ("remove jumps", remove-jumps, interp-x86-2)
    ("patch instructions" ,patch-instructions ,interp-x86-2)
    ("kill unused blocks", kill-unused-blocks, interp-x86-2)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-2)
    ))
