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
(require "interp-Llambda.rkt")
(require "interp-Llambda-prime.rkt")
(require "interp-Clambda.rkt")
(require "type-check-Llambda.rkt")
(require "type-check-Clambda.rkt")
(provide (all-defined-out))

;; Shulin Calvin and I discuss our solutions
;; but we each work independently and have our
;; own personal solutions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General purpose helper functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (id x) x)

(define (dict-filter p d)
  (cond ((dict-empty? d) d)
        (else (define k (car (dict-keys d)))
              (if (p k (dict-ref d k))
                  (dict-set (dict-filter p (dict-remove d k)) k (dict-ref d k))
                  (dict-filter p (dict-remove d k))))))

(define (dict-combine-key k d1 d2)
  (define v1 (dict-ref d1 k))
  (define v2 (dict-ref d2 k))
  (cond
    ((list? v1) (append v1 v2))
    ((set?  v1) (set-union v1 v2))
    (else v1)))

(define (dict-append-two d1 d2)
  (cond
    ((dict-empty? d1) d2)
    (else (define k (car (dict-keys d1)))
          (dict-append-two (dict-remove d1 k) (if (dict-has-key? d2 k)
                                                  (dict-set d2 k (dict-combine-key k d1 d2))
                                                  (dict-set d2 k (dict-ref d1 k)))))))

(define (dict-append . ds)
  (match ds
    ['() '()]
    [(cons d '()) d]
    [(cons d ds) (dict-append-two d (apply dict-append ds))]))

(define (flip-dict d empty-dict)
   (foldr (λ (x d) (dict-set d (cdr x) (car x))) empty-dict (dict->list d)))

(define (rec-exprs e f)
  (match e
    [(Let x e body) (Let x (f e) (f body))]
    [(If e1 e2 e3) (If (f e1) (f e2) (f e3))]
    [(Prim op es) (Prim op (for/list ([e es]) (f e)))]
    [(SetBang v e) (SetBang v (f e))]
    [(Begin es ef) (Begin (for/list ([e es]) (f e)) (f ef))]
    [(WhileLoop c b) (WhileLoop (f c) (f b))]
    [(AllocateArray e t) (AllocateArray (f e) t)]
    [(Apply e es) (Apply (f e) (for/list ([e es]) (f e)))]
    [(HasType v t) (HasType (f v) t)]
    [(Lambda ts t b) (Lambda ts t (f b))]
    [(UncheckedCast v t) (UncheckedCast (f v) t)]
    [_ e]))

(define ds-methods (dict-set* '() 'list (dict-set* '() 'union append      'empty '())
                                  'set  (dict-set* '() 'union set-union   'empty (set))
                                  'dict (dict-set* '() 'union dict-append 'empty '())))

(define (rec-exprs-ds e f ds)
  (match e
    [(Let v e1 e2) ((dict-ref (dict-ref ds-methods ds) 'union) (f e1) (f e2))]
    [(If e1 e2 e3) ((dict-ref (dict-ref ds-methods ds) 'union) (f e1) ((dict-ref (dict-ref ds-methods ds) 'union)
                                                                       (f e2) (f e3)))]
    [(Prim op es)  (for/fold ([recs (dict-ref (dict-ref ds-methods ds) 'empty)]) ([e es])
                     ((dict-ref (dict-ref ds-methods ds) 'union) (f e) recs))]
    [(SetBang v e) (f e)]
    [(Begin es ef) ((dict-ref (dict-ref ds-methods ds) 'union)
                    (for/fold ([recs (dict-ref (dict-ref ds-methods ds) 'empty)]) ([e es])
                      ((dict-ref (dict-ref ds-methods ds) 'union) (f e) recs)) (f ef))]
    [(WhileLoop c b) ((dict-ref (dict-ref ds-methods ds) 'union) (f c) (f b))]
    [(AllocateArray e t) (f e)]
    [(Apply af es) ((dict-ref (dict-ref ds-methods ds) 'union)
                    (f af) (for/fold ([recs (dict-ref (dict-ref ds-methods ds) 'empty)]) ([e es])
                             ((dict-ref (dict-ref ds-methods ds) 'union) (f e) recs)))]
    [(HasType v t) (f v)]
    [(Lambda ps t body) (f body)]
    [(UncheckedCast v t) (f v)]
    [_ (dict-ref (dict-ref ds-methods ds) 'empty)]))

(define (match-defs ds base-ret recur)
  (match ds
    ['() base-ret]
    [(cons (Def v ts t i e) ds) (recur v ts t i e ds)]))

(define (rec-defs ds f) (match-defs ds '() (λ (v ts t i e ds) (cons (Def v ts t i (f e)) (rec-defs ds f)))))
(define (rec-defs-new-def ds f) (match-defs ds '() (λ (v ts t i e ds) (cons (f v ts t i e) (rec-defs-new-def ds f)))))

(define (number->symbol n) (string->symbol (number->string n)))

(define (get-fun-args ts) (map (λ (ty) (match ty [`[,x : ,t] x])) ts))
(define (get-fun-arg-tys ts) (map (λ (ty) (match ty [`[,x : ,t] t])) ts))

(define (type-check-Llambda-typed-vars p)
  (typed-vars #t) (define t (type-check-Llambda p)) (typed-vars #f) t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Partial Evaluation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (cmp? op) (or (equal? op 'eq?) (equal? op '<) (equal? op '<=) (equal? op '>) (equal? op '>=)))
(define (cmp->cmp-func cmp) (match cmp ['< <] ['> >] ['<= <=] ['>= >=] ['eq? eq?]))

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
    [(Program info e) (Program info (pe-exp e (make-hash)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eradicate structs : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Using Function as a stand in StructFunction since ag doesn't have StructFunction
(define (struct->funcs defs)
  (match defs
    ['() '()]
    [(cons (StructDef s (list `[,xs : ,ps] ...)) defs)
     (append (append (list (cons s (Function 'init '() #f)))
                     (let ((i -1))
                       (for/list [(x xs)] (cons (symbol-append 'set- (symbol-append
                                                                      s (symbol-append '- (symbol-append x '!))))
                                                (begin
                                                  (set! i (add1 i))
                                                  (Function 'set! (list (Int i)) #f)))))
                     (let ((i -1))
                       (for/list [(x xs)] (cons (symbol-append s (symbol-append '- x))
                                                (begin
                                                  (set! i (add1 i))
                                                  (Function 'ref (list (Int i)) #f))))))
             (struct->funcs defs))]
    [(cons _ defs) (struct->funcs defs)]))

(define (eradicate-structs-expr env)
  (λ (e)
    (match e
      [(Apply (Var func) args)
       #:when (dict-has-key? env func)
       (match-let (((Function method struct-args #f) (dict-ref env func)))
         (match method
           ['init (Prim 'vector (for/list [(a args)] ((eradicate-structs-expr env) a)))]
           ['set! (Prim 'vector-set! (for/list [(a (list (first args) (first struct-args) (second args)))]
                                       ((eradicate-structs-expr env) a)))]
           ['ref  (Prim 'vector-ref (for/list [(a (list (first args) (first struct-args)))]
                                      ((eradicate-structs-expr env) a)))]))]
      [_ (rec-exprs e (eradicate-structs-expr env))])))

(define (remove-struct-def defs)
  (match defs
    ['() '()]
    [(cons (StructDef _ _) defs) (remove-struct-def defs)]
    [(cons a defs) (cons a (remove-struct-def defs))]))

(define (eradicate-structs p)
  (match p
    [(ProgramDefsExp info defs e) (ProgramDefsExp info (remove-struct-def defs)
                                                       ((eradicate-structs-expr (struct->funcs defs)) e))]
    [else p]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; shrink : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (shrink-exp e)
  (match e
    [(Prim 'and (list e1 e2)) (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or (list e1 e2)) (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [_ (rec-exprs e shrink-exp)]))

(define (shrink p)
  (match p
    [(Program info e) (ProgramDefs info (list (Def 'main '() 'Integer '() (shrink-exp e))))]
    [(ProgramDefsExp info defs e) (ProgramDefs info (rec-defs (cons (Def 'main '() 'Integer '() e) defs) shrink-exp))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uniquify : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define unique-number 0)
(define (uniquify-name x)
  (begin
    (set! unique-number (add1 unique-number))
    (symbol-append (racket-id->c-id x) (symbol-append (string->symbol ".") (number->symbol unique-number)))))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(SetBang v e) (SetBang (dict-ref env v) ((uniquify-exp env) e))]
      [(Let x e body)
       (define new-name (uniquify-name x))
       (Let new-name ((uniquify-exp env) e) ((uniquify-exp (dict-set env x new-name)) body))]
      [(Lambda ts t b)
       (define new-args (map uniquify-name (get-fun-args ts)))
       (Lambda (for/list ([arg^ new-args] [t (get-fun-arg-tys ts)]) `(,arg^ : ,t))
               t ((uniquify-exp (for/fold ([env^ env])
                                          ([arg (get-fun-args ts)]
                                           [arg^ new-args])
                                  (dict-set env^ arg arg^))) b))]
      [_ (rec-exprs e (uniquify-exp env))])))

(define (init-env defs)
  (match-defs defs (make-immutable-hash)
              (λ (v ts t i e defs) (if (equal? v 'main) (dict-set (init-env defs) 'main 'main)
                                       (dict-set (init-env defs) v (uniquify-name v))))))

(define (uniquify-args env)
  (λ (args)
    (match args
      ['() (values env '())]
      [(cons `[,v : ,t] args) (define-values (env^ args^) ((uniquify-args env) args))
                              (define new-name (uniquify-name v))
                              (values (dict-set env^ v new-name) (cons `[,new-name : ,t] args^))])))

(define (uniquify-defs env)
  (λ (defs)
    (match-defs defs '() (λ (v ts t i e defs)
                           (define-values (env^ ts^) ((uniquify-args env) ts))
                           (cons (Def (dict-ref env^ v) ts^ t i ((uniquify-exp env^) e))
                                 ((uniquify-defs env^) defs))))))

(define (uniquify p)
  (set! unique-number 0)
  (match-let [((ProgramDefs info defs) p)]
    (ProgramDefs info ((uniquify-defs (init-env defs)) defs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; resolve : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (get-type e env)
  (if (dict-has-key? env e)
      (dict-ref env (extract-var-ht e))
      (match e [(HasType v t) t] [else #f])))

(define (extract-var-ht e)
  (match e [(HasType v t) v] [else e]))

(define (resolve-exp e)
  (match e
    [(HasType v t) v]
    [(Prim 'vector-ref (list (HasType v t) e))
     #:when (equal? 'Vectorof (car t))
     (Prim 'vectorof-ref (list (resolve-exp v) (resolve-exp e)))]
    [(Prim 'vector-set! (list (HasType v t) e1 e2))
     #:when (equal? 'Vectorof (car t))
     (Prim 'vectorof-set! (list (resolve-exp v) (resolve-exp e1) (resolve-exp e2)))]
    [(Prim 'vector-length (list (HasType v t)))
     #:when (equal? 'Vectorof (car t))
     (Prim 'vectorof-length (list (resolve-exp v)))]
    [_ (rec-exprs e resolve-exp)]))

(define (resolve p)
  (match-let [((ProgramDefs info defs) p)]
    (ProgramDefs info (rec-defs defs resolve-exp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; check-bounds : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (check-vec v i op args)
  (If (Prim '< (list i (Prim 'vectorof-length (list v))))
      (Prim op args)
      (Prim 'exit '())))

(define (check-bounds-exp e)
  (match e
    [(Prim 'vectorof-set! (list v i e2))
     (define v^ (check-bounds-exp v))
     (define i^ (check-bounds-exp i))
     (check-vec v^ i^ 'vectorof-set! (list v^ i^ (check-bounds-exp e2)))]
    [(Prim 'vectorof-ref (list v i))
     (define v^ (check-bounds-exp v))
     (define i^ (check-bounds-exp i))
     (check-vec v^ i^ 'vectorof-ref (list v^ i^))]
    [_ (rec-exprs e check-bounds-exp)]))

(define (check-bounds p)
  (match-let [((ProgramDefs info defs) p)]
    (ProgramDefs info (rec-defs defs check-bounds-exp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reveal-functions : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (reveal-functions-exp env)
  (λ (e)
    (match e
      [(Var v) #:when (dict-has-key? env v) (FunRef v (dict-ref env v))]
      [_ (rec-exprs e (reveal-functions-exp env))])))

(define (init-functions-env ds)
  (match-defs ds (make-immutable-hash) (λ (v ts t i e ds) (dict-set (init-functions-env ds) v (length ts)))))

(define (reveal-functions p)
  (match-let [((ProgramDefs info defs) p)]
    (ProgramDefs info (rec-defs defs (reveal-functions-exp (init-functions-env defs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; convert-assignments : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (free-vars bound)
  (λ (e)
    (match e
      [(HasType (Var x) t) (if (set-member? bound x) '() (list (cons x t)))]
      [(Let v e1 e2) (dict-append ((free-vars bound) e1) ((free-vars (set-add bound v)) e2))]
      [(Lambda ts t b) ((free-vars (set-union bound (list->set (get-fun-args ts)))) b)]
      [_ (rec-exprs-ds e (free-vars bound) 'dict)])))

(define (free-in-lambda e)
  (match e
    [(Lambda ts t b) ((free-vars (list->set (get-fun-args ts))) b)]
    [_ (rec-exprs-ds e free-in-lambda 'dict)]))

(define (convert-assignments-expr af)
  (λ (e)    
    (match e
      [(HasType (Var x) t) #:when (set-member? af x) (Prim 'vector-ref (list (Var (symbol-append x '_0)) (Int 0)))]
      [(HasType (Var x) t) (Var x)]
      [(Let v e1 e2) #:when (set-member? af v)
                     (Let (symbol-append v '_0)
                          (Prim 'vector (list ((convert-assignments-expr af) e1)))
                          ((convert-assignments-expr af) e2))]
      [(SetBang x e) #:when (set-member? af x)
                     (Prim 'vector-set! (list (Var (symbol-append x '_0)) (Int 0) ((convert-assignments-expr af) e)))]
      [(Lambda ts t b) ((convert-assignments-def (set-union af (get-af b))) #f ts t #f b)]
      [_ (rec-exprs e (convert-assignments-expr af))])))

(define (fold-let-assignments ts e af)
  (for/fold ([l-exprs ((convert-assignments-expr af) e)]) ([v (filter (λ (v) (member v (get-fun-args ts)))
                                                                 (set->list af))])
    (Let (symbol-append v '_0) (Prim 'vector (list (Var v))) l-exprs)))

(define (get-af e) (set-intersect (list->set (dict-keys (free-in-lambda e))) (collect-set! e)))

(define (convert-assignments-def af^)
  (λ (v ts t i e)
    (define af (if af^ af^ (get-af e)))
    (if v (Def v ts t i (fold-let-assignments ts e af))
          (Lambda ts t (fold-let-assignments ts e af)))))

(define (convert-assignments p)
  (match-let [((ProgramDefs info defs) p)]
    (ProgramDefs info (rec-defs-new-def defs (convert-assignments-def #f)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; closure-conversion : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define lambda-defs '())
(define (function-type? t) (match t [`(,ps ... -> ,rt) #t] [else #f]))
(define (translate-type t)
  (cond
    ((function-type? t) `(Vector ,(cons '(Vector _) (map translate-type t))))
    ((list? t) (map translate-type t))
    (else t)))

(define (translate-types ts)
  (for/list ([a (get-fun-args ts)]
             [t^ (map translate-type (get-fun-arg-tys ts))])
    `[,a : ,t^]))

(define (closure-exp escapees)
  (λ (e)    
    (match e
      [(Lambda ts t b)
       (define name (uniquify-name 'lambda))
       (define fvs/ts (free-in-lambda e))
       (define fvs (reverse (dict-keys fvs/ts)))
       (define fvts (reverse (dict-values fvs/ts)))
       (define def (Def name (cons `[clos : ,(append '(Vector _) (map translate-type fvts))]
                                   (translate-types ts))
                     (translate-type t) '()
                     (for/fold ([l-exprs ((closure-exp escapees) b)]) ([fv fvs] [i (range (length fvs))])
                       (Let fv (Prim 'vector-ref (list (Var 'clos) (Int (add1 i)))) l-exprs))))
       (set! lambda-defs (cons def lambda-defs))
       (Closure (length ts) (cons (FunRef name (length ts)) (map Var fvs)))]
      [(Apply (FunRef f n) es) #:when (not (set-member? escapees f))
                               (Apply (FunRef f n) (for/list ([e es]) ((closure-exp escapees) e)))]
      [(Apply (HasType (Var x) t) es)
       (Apply (Prim 'vector-ref (list (Var x) (Int 0)))
              (cons (Var x) (for/list ([e es]) ((closure-exp escapees) e))))]
      [(Apply e es)
       (define tmp (uniquify-name 'clos))
       (Let tmp ((closure-exp escapees) e) (Apply (Prim 'vector-ref (list (Var tmp) (Int 0)))
                                                  (cons (Var tmp) (for/list ([e es]) ((closure-exp escapees) e)))))]
      [(FunRef f n) #:when (set-member? escapees f) (Closure n (cons (FunRef f n) '()))]
      [(HasType (Var x) t) (Var x)]
      [_ (rec-exprs e (closure-exp escapees))])))

(define (closure-def escapees)
  (λ (v ts t i e)
    (Def v (if (not (set-member? escapees v)) (translate-types ts)
               (cons '[clos : _] (translate-types ts)))
      (translate-type t) i ((closure-exp escapees) e))))

(define (escaped-defs ds)
  (match-defs ds (set) (λ (v ts t i e ds) (set-union (escaped-calls e) (escaped-defs ds)))))

(define (escaped-calls e)
  (match e
    [(FunRef f a) (set f)]
    [(Apply (FunRef f a) es) (for/fold ([recs (set)]) ([e es])
                               (set-union (escaped-calls e) recs))]
    [_ (rec-exprs-ds e escaped-calls 'set)]))

(define (closure-conversion p)
  (set! lambda-defs '())
  (match-let [((ProgramDefs info defs) p)]
    (define defs^ (rec-defs-new-def defs (closure-def (escaped-defs defs))))
    (ProgramDefs info (append lambda-defs defs^))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; optimize-known-calls : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (okc-expr env)
  (λ (e)
    (match e
      [(Let v (HasType (Closure l (cons (FunRef name a) fvs)) t) e)
       (Let v (Closure l (cons (FunRef name a) fvs)) ((okc-expr (dict-set env v (cons name a))) e))]
      [(Apply (Prim 'vector-ref (list (Var clos) (Int 0))) es)
       #:when (dict-has-key? env clos)
       (define name/arity (dict-ref env clos))
       (Apply (FunRef (car name/arity) (cdr name/arity)) (for/list ([e es]) ((okc-expr env) e)))]
      [_ (rec-exprs e (okc-expr env))])))

(define (optimize-known-calls p)
  (match-let [((ProgramDefs info defs) p)]
    (ProgramDefs info (rec-defs defs (okc-expr '())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; limit-functions : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define n-arg-regs (vector-length arg-registers))

(define (limit-functions-exp e)
  (match e
    [(Closure n (list (FunRef f i))) #:when (> n n-arg-regs) (Closure n (list (FunRef f n-arg-regs)))]
    [(Apply (FunRef f i) es)
     #:when (> i n-arg-regs)
     (Apply (FunRef f n-arg-regs) (append (take es (sub1 n-arg-regs)) (list (Prim 'vector (drop es (sub1 n-arg-regs))))))]
    [(Apply c es)
     #:when (> (length es) n-arg-regs)
     (Apply c (append (take es (sub1 n-arg-regs)) (list (Prim 'vector (drop es (sub1 n-arg-regs))))))]
    [_ (rec-exprs e limit-functions-exp)]))

(define (init-limit-env ts tup i)
  (match ts
    ['() (make-immutable-hash)]
    [(cons `[,x : ,t] ts) (dict-set (init-limit-env ts tup (add1 i)) x (Prim 'vector-ref (list (Var tup) (Int i))))]))

(define (limit-functions-replace-defs env)
  (λ (e)
    (match e
      [(Var x) #:when (dict-has-key? env x) (dict-ref env x)]
      [_ (rec-exprs e (limit-functions-replace-defs env))])))

(define (limit-functions-defs defs)
  (match defs
    ['() '()]
    [(cons (Def v ts t i e) defs)
     #:when (> (length ts) n-arg-regs)
     (define tup-name (uniquify-name 'limit-tup))
     (cons (Def v (append (take ts (sub1 n-arg-regs))
                          (list `[,tup-name : (Vector ,@(drop (get-fun-arg-tys ts) (sub1 n-arg-regs)))]))
             t i ((limit-functions-replace-defs (init-limit-env (drop ts (sub1 n-arg-regs)) tup-name 0)) e))
           (limit-functions-defs defs))]
    [(cons d defs) (cons d (limit-functions-defs defs))]))

(define (limit-functions p)
  (match-let [((ProgramDefs info defs) p)]
    (ProgramDefs info (rec-defs (limit-functions-defs defs) limit-functions-exp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; expose-allocation : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (collect-check num-bytes)
  (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr)
                                    num-bytes))
                     (GlobalValue 'fromspace_end)))
      (Void)
      (Collect num-bytes)))

(define (vector-set-tuple mapping vec idx [type-cast #f])
  (match mapping
    ['() (if type-cast (UncheckedCast (Var vec) type-cast) (Var vec))]
    [(cons (cons v e) mapping)
     (Let '_ (Prim 'vector-set! (list (Var vec) (Int idx) (Var v)))
             (vector-set-tuple mapping vec (add1 idx) type-cast))]))

(define (collect/alloc-tuple len num-bytes alloc-label type mapping)
  (Let '_ (collect-check (Int num-bytes))
       (Let alloc-label (Allocate len type)
            (vector-set-tuple mapping alloc-label 0))))

(define (create-tuple vs type mapping)
  (match vs
    ['() (collect/alloc-tuple (length mapping) (* 8 (add1 (length mapping))) (uniquify-name 'alloc) type mapping)]
    [(cons v vs)
     (define label (uniquify-name 'vecinit))
     (Let label (expose-expr v) (create-tuple vs type (dict-set mapping label v)))]))

(define (vector-set-array idx len ini vec)
  (define ini^ (uniquify-name 'arr-ini))
  (Let idx (Int 0)
       (Let ini^ ini
            (Begin (list (WhileLoop (Prim '< (list (Var idx) len))
                                    (Begin (list (Prim 'vector-set! (list (Var vec) (Var idx) (Var ini^))))
                                           (SetBang idx (Prim '+ (list (Var idx) (Int 1)))))))
                   (Var vec)))))

(define (create-array len ini type alloc-label)
  (Let '_ (collect-check (Prim '* (list (Int 8) (Prim '+ (list (Int 1) len)))))
       (Let alloc-label (AllocateArray len type)
            (vector-set-array (uniquify-name 'idx) len ini alloc-label))))

(define (collect/alloc-clos arity len num-bytes alloc-label type mapping)
  (Let '_ (collect-check (Int num-bytes))
       (Let alloc-label (AllocateClosure len type arity)
            (vector-set-tuple mapping alloc-label 0 `(Vector ((Vector _) ,@(cdadr type)))))))

(define (create-clos arity args type mapping)
  (match args
    ['() (collect/alloc-clos arity (length mapping) (* 8 (add1 (length mapping))) (uniquify-name 'allocclos) type mapping)]
    [(cons arg args)
     (define label (uniquify-name 'closinit))
     (Let label (expose-expr arg) (create-clos arity args type (dict-set mapping label arg)))]))

(define (expose-expr e)
  (match e
    [(HasType (Prim 'vector vs) type) (create-tuple vs type '())]
    [(HasType (Prim 'make-vector (list len ini)) type)
     (create-array (expose-expr len) (expose-expr ini) type (uniquify-name 'alloc))]
    [(HasType (Closure n es) type) (create-clos n es type '())]
    [_ (rec-exprs e expose-expr)]))

(define (expose-allocation p)
  (match-let  [((ProgramDefs info defs) p)]
    (ProgramDefs info (rec-defs defs expose-expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover-get! : L -> L
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (collect-set! e)
  (match e
    [(SetBang v e) (set-union (set v) (collect-set! e))]
    [_ (rec-exprs-ds e collect-set! 'set)]))

(define (uncover-get!-expr set!-vars e)
  (match e
    [(Var x) (if (set-member? set!-vars x) (GetBang x) (Var x))]
    [_ (rec-exprs e (λ (e) (uncover-get!-expr set!-vars e)))]))

(define (uncover-get! p)
  (match-let [((ProgramDefs info defs) p)]
    (ProgramDefs info (rec-defs defs (λ (e) (uncover-get!-expr (collect-set! e) e))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remove-complex-opera* : L -> L^mon
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (atom? e) (match e [(Int i) #:when (<= i (expt 2 32)) #t]
                           [(Var v) #t] [(Bool b) #t] [(Void) #t] [else #f]))

(define (rco-atom e k)
  (match e
    [_ #:when (atom? e) (k e)]
    [_ (define tmp (uniquify-name 'tmp))
       (Let tmp (rco-exp e) (k (Var tmp)))]))

(define (build-atm-cont xs k)
  (match xs
    ['() (k '())]
    [(cons x xs) (rco-atom x (λ (v) (build-atm-cont xs (λ (rst) (k (cons v rst))))))]))

(define (rco-exp e)
  (match e
    [(Prim op es) (build-atm-cont es (λ (vs) (Prim op vs)))]
    [(Collect e) (rco-atom e (λ (v) (Collect v)))]
    [(AllocateArray e t) (rco-atom e (λ (v) (AllocateArray v t)))]
    [(Apply e es) (rco-atom e (λ (v) (build-atm-cont es (λ (vs) (Apply v vs)))))]
    [_ (rec-exprs e rco-exp)]))

(define (remove-complex-opera* p)
  (match-let [((ProgramDefs info defs) p)]
      (ProgramDefs info (rec-defs defs rco-exp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; explicate-control : L^mon -> C
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define basic-blocks (make-immutable-hash))
(define (create-block tail)
  (delay
    (match (force tail)
      [(Goto label) (Goto label)]
      [else
       (define label (uniquify-name 'block))
       (set! basic-blocks (dict-set basic-blocks label (force tail)))
       (Goto label)])))

(define (explicate-loop c b cont)
  (define loop (uniquify-name 'loop))
  (define body (explicate-effect b (Goto loop)))
  (define cnd  (explicate-pred c body cont))
  (set! basic-blocks (dict-set basic-blocks loop cnd))
  (Goto loop))

(define (explicate-tail e)
  (delay
    (force
     (match e
       [(If p bt bf) (explicate-pred p (explicate-tail bt) (explicate-tail bf))]
       [(Let x rhs body) (explicate-assign x rhs (explicate-tail body))]
       [(WhileLoop c b) (explicate-loop c b (Return (Void)))]
       [(SetBang v e) (explicate-assign v e)]
       [(Begin es ef) (foldr explicate-effect (explicate-tail ef) es)]
       [(GetBang x) (Return (Var x))]
       [(Apply e es) (TailCall e es)]
       [_ (Return e)]))))

(define (explicate-assign x e cont)
  (match e
    [(GetBang x^) (Seq (Assign (Var x) (Var x^)) (force cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) (force cont))]
    [(If p bt bf)
     (define block (create-block cont))
     (explicate-pred p (delay (explicate-assign x bt block)) (delay (explicate-assign x bf block)))]
    [(Let y rhs body) (explicate-assign y rhs (explicate-assign x body cont))]
    [(WhileLoop c b) (explicate-loop c b (Seq (Assign (Var x) (Void)) (force cont)))]
    [(SetBang v e) (Seq (explicate-assign v e) (Seq (Assign (Var x) (Void)) (force cont)))]
    [(Begin es ef) (foldr explicate-effect (explicate-assign x ef cont) es)]
    [(Collect i) (Seq (Collect i) (Seq (Assign (Var x) (Void)) (force cont)))]
    [(Apply e es) (Seq (Assign (Var x) (Call e es)) (force cont))]
    [_ (Seq (Assign (Var x) e) (force cont))]))

(define (explicate-pred p bt bf)
  (match p
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (force (create-block bt)) (force (create-block bf)))]
    [(GetBang x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (force (create-block bt)) (force (create-block bf)))]
    [(Bool b) (if b (force bt) (force bf))]
    [(Let x rhs body) (explicate-assign x rhs (explicate-pred body bt bf))]
    [(Prim 'not (list (Bool b))) (if (not b) (force bt) (force bf))]
    [(Prim 'not (list e)) (IfStmt (Prim 'eq? (list e (Bool #f))) (force (create-block bt)) (force (create-block bf)))]
    [(Prim 'vector-ref (list e1 e2)) (pred-assign 'pred-vec-ref p bt bf)]
    [(Prim op es) (IfStmt (Prim op es) (force (create-block bt)) (force (create-block bf)))]
    [(If p^ bt^ bf^)
     (define true-block (create-block bt))
     (define false-block (create-block bf))
     (explicate-pred p^ (delay (explicate-pred bt^ true-block false-block))
                        (delay (explicate-pred bf^ true-block false-block)))]
    [(Begin es ef) (foldr explicate-effect (explicate-pred ef bt bf) es)]
    [(Apply e es) (pred-assign 'pred-call (Call e es) bt bf)]))

(define (pred-assign name p bt bf)
  (define tmp (uniquify-name name))
  (explicate-assign tmp p (IfStmt (Prim 'eq? (list (Var tmp) (Bool #t)))
                                  (force (create-block bt)) (force (create-block bf)))))

(define (combine-side-effects se)
  (cons (foldr (λ (a b) (or (car a) b)) #f se)
        se))

(define (get-side-effect e)
  (match e
    [(SetBang v e) (cons #t (list #t))]
    [(Prim 'read '()) (cons #t (list #t))]
    [(Prim 'print (list e)) (cons #t (list #t))]
    [(Prim 'vector-set! (list e1 e2 e3)) (cons #t (list #t))]
    [(Prim 'vectorof-set! (list e1 e2 e3)) (cons #t (list #t))]
    [(Apply f es) (cons #t (list #t))]
    [(Prim op es) (combine-side-effects (map get-side-effect es))]
    [(Let v e1 e2) (combine-side-effects (list (get-side-effect e1) (get-side-effect e2)))]
    [(If p bt bf) (combine-side-effects (list (get-side-effect p) (get-side-effect bt) (get-side-effect bf)))]
    [(WhileLoop c b) (combine-side-effects (list (get-side-effect c) (get-side-effect b)))]
    [(Begin es ef) (combine-side-effects (append (map get-side-effect es) (list (get-side-effect ef))))]
    [_ (cons #f (list #f))]))

(define (explicate-effect e cont [se #f])
  (define side-effects (if se se (get-side-effect e)))
  (if (not (car side-effects)) ;; no side effects anywhere
      (force cont)
      (match e
        [(Prim 'read '()) (Seq (Prim 'read '()) (force cont))]
        [(Prim 'print (list e)) (Seq (Prim 'print (list e)) (force cont))]
        [(Prim 'vector-set! (list e1 e2 e3)) (Seq (Prim 'vector-set! (list e1 e2 e3)) (force cont))]
        [(Prim 'vectorof-set! (list e1 e2 e3)) (Seq (Prim 'vectorof-set! (list e1 e2 e3)) (force cont))]
        [(Apply e es) (Seq (Apply e es) (force cont))]
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

(define (explicate-control-def d v)
  (set! basic-blocks (make-immutable-hash))
  (define start (force (explicate-tail d)))
  (dict-set basic-blocks (symbol-append v '_start) start))

(define (explicate-control-defs ds)
  (match-defs ds '() (λ (v ts t i e ds) (cons (Def v ts t i (explicate-control-def e v))
                                              (explicate-control-defs ds)))))

(define (explicate-control p)
  (match-let (((ProgramDefs info defs) p))
    (ProgramDefs info (explicate-control-defs defs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; select-instructions : C -> x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (select-atm e)
  (match e
    [(Int n) (Imm n)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(Void) (Imm 0)]
    [(GlobalValue v) (Global v)]
    [(UncheckedCast v t) v]
    [_ e]))

(define (get-cc op)
  (match op ['eq? 'e] ['< 'l] ['<= 'le] ['> 'g] ['>= 'ge]))

(define (get-ptr-mask type)
  (match type
    ['() 0]
    [(cons t type) (+ (if (list? t) 1 0) (* 2 (get-ptr-mask type)))]))

(define (init-tag n type)
  (+ 1 (arithmetic-shift (get-ptr-mask (cdr type)) 7) (arithmetic-shift n 1)))

(define (init-tag-clos n type arity)
  (+ (+ 1 (arithmetic-shift (get-ptr-mask (cddr type)) 8) (arithmetic-shift n 1))
     (arithmetic-shift arity 57)))

(define (select-two-arg-prim op a1 a2 x)
  (cond ((equal? a1 x) (list (Instr op (list (select-atm a2) x))))
        ((equal? a2 x) (list (Instr op (list (select-atm a1) x))))
        (else (list (Instr 'movq (list (select-atm a1) x))
                    (Instr op (list (select-atm a2) x))))))

(define (select-expr x e)
  (match e
    [(Prim 'read '())
     (list (Callq 'read_int 0)
           (Instr 'movq (list (Reg 'rax) x)))]
    [(Prim 'print (list e))
     (list (Instr 'movq (list (select-atm e) (Reg 'rdi)))
           (Callq 'print_int 1)
           (Instr 'movq (list (Reg 'rax) x)))]
    [(Prim 'exit '())
     (list (Instr 'movq (list (Imm 255) (Reg 'rdi)))
           (Callq 'exit 1))]
    [(Prim '- (list a))
     (if (equal? a x)
         (list (Instr 'negq (list x)))
         (list (Instr 'movq (list (select-atm a) x))
               (Instr 'negq (list x))))]
    [(Prim '+ (list a1 a2)) (select-two-arg-prim 'addq  a1 a2 x)]
    [(Prim '- (list a1 a2)) (select-two-arg-prim 'subq  a1 a2 x)]
    [(Prim '* (list a1 a2)) (select-two-arg-prim 'imulq a1 a2 x)]
    [(Prim 'not (list e))   (select-two-arg-prim 'xorq (Imm 1) x)]
    [(Prim op (list e1 e2))
     #:when (cmp? op)
     (list (Instr 'cmpq (list (select-atm e2) (select-atm e1)))
           (Instr 'set (list (get-cc op) (ByteReg 'al)))
           (Instr 'movzbq (list (ByteReg 'al) x)))]
    [(Prim 'vector-ref (list tup (Int n)))
     (list (Instr 'movq (list (select-atm tup) (Reg 'r11)))
           (Instr 'movq (list (Deref 'r11 (* 8 (add1 n))) x)))]
    [(Prim 'vector-set! (list tup (Int n) rhs))
     (list (Instr 'movq (list (select-atm tup) (Reg 'r11)))
           (Instr 'movq (list (select-atm rhs) (Deref 'r11 (* 8 (add1 n)))))
           (Instr 'movq (list (Imm 0) x)))]
    [(Prim 'vector-length (list tup))
     (list (Instr 'movq (list (select-atm tup) (Reg 'r11)))
           (Instr 'movq (list (Deref 'r11 0) x))
           (Instr 'andq (list (Imm #x7E) x))
           (Instr 'sarq (list (Imm 1) x)))]
    [(Prim 'vectorof-ref (list arr e))
     (list (Instr 'movq  (list (select-atm arr) (Reg 'r11)))
           (Instr 'movq  (list (select-atm e) (Reg 'rax)))
           (Instr 'addq  (list (Imm 1) (Reg 'rax)))
           (Instr 'imulq (list (Imm 8) (Reg 'rax)))
           (Instr 'addq  (list (Reg 'rax) (Reg 'r11)))
           (Instr 'movq  (list (Deref 'r11 0) x)))]
    [(Prim 'vectorof-set! (list arr e rhs))
     (list (Instr 'movq  (list (select-atm arr) (Reg 'r11)))
           (Instr 'movq  (list (select-atm e) (Reg 'rax)))
           (Instr 'addq  (list (Imm 1) (Reg 'rax)))
           (Instr 'imulq (list (Imm 8) (Reg 'rax)))
           (Instr 'addq  (list (Reg 'rax) (Reg 'r11)))
           (Instr 'movq  (list (select-atm rhs) (Deref 'r11 0)))
           (Instr 'movq  (list (Imm 0) x)))]
    [(Prim 'vectorof-length (list arr))
     (list (Instr 'movq (list (select-atm arr) (Reg 'r11)))
           (Instr 'movq (list (Deref 'r11 0) x))
           (Instr 'movq (list (Imm #x3FFFFFFFFFFFFFFC) (Reg 'r11)))
           (Instr 'andq (list (Reg 'r11) x))
           (Instr 'sarq (list (Imm 2) x)))]
    [(Prim 'procedure-arity (list proc))
     (list (Instr 'movq (list (select-atm proc) (Reg 'r11)))
           (Instr 'movq (list (Deref 'r11 0) x))
           (Instr 'sarq (list (Imm 57) x)))]
    [(Allocate n type)
     (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
           (Instr 'addq (list (Imm (* 8 (add1 n))) (Global 'free_ptr)))
           (Instr 'movq (list (Imm (init-tag n type)) (Deref 'r11 0)))
           (Instr 'movq (list (Reg 'r11) x)))]
    [(AllocateClosure len type arity)
     (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
           (Instr 'addq (list (Imm (* 8 (add1 len))) (Global 'free_ptr)))
           (Instr 'movq (list (Imm (init-tag-clos len type arity)) (Deref 'r11 0)))
           (Instr 'movq (list (Reg 'r11) x)))]
    [(AllocateArray e type)
     (list (Instr 'movq  (list (select-atm e) (Reg 'rax)))
           (Instr 'salq  (list (Imm 2) (Reg 'rax)))
           (Instr 'addq  (list (Imm (if (list? (car type)) 3 1)) (Reg 'rax)))
           (Instr 'movq  (list (Imm (arithmetic-shift 1 62)) (Reg 'r11)))
           (Instr 'addq  (list (Reg 'r11) (Reg 'rax))) 
           (Instr 'movq  (list (Global 'free_ptr) (Reg 'r11)))
           (Instr 'movq  (list (Reg 'rax) (Deref 'r11 0)))
           (Instr 'movq  (list (select-atm e) (Reg 'rax)))
           (Instr 'addq  (list (Imm 1) (Reg 'rax)))
           (Instr 'imulq (list (Imm 8) (Reg 'rax)))
           (Instr 'addq  (list (Reg 'rax) (Global 'free_ptr)))
           (Instr 'movq  (list (Reg 'r11) x)))]
    [(FunRef f n)
     (list (Instr 'leaq (list (Global f) (Reg 'rax)))
           (Instr 'movq (list (Reg 'rax) x)))]
    [(Call f args)
     (append (init-args args (take (map Reg (vector->list arg-registers)) (length args)))
             (list (IndirectCallq f (length args))
                   (Instr 'movq (list (Reg 'rax) x))))]
    [else (list (Instr 'movq (list (select-atm e) x)))]))

(define (select-stmt e)
  (match e
    [(Assign (Var x) e) (select-expr (Var x) e)]
    [(Prim 'read '()) (list (Callq 'read_int 0))]
    [(Prim 'print (list e)) (list (Instr 'movq (list (select-atm e) (Reg 'rdi)))
                                  (Callq 'print_int 1))]
    [(Collect b) (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
                       (Instr 'movq (list (select-atm b) (Reg 'rsi)))
                       (Callq 'collect 2))]
    [(Prim 'vector-set! (list tup (Int n) rhs))
     (list (Instr 'movq (list (select-atm tup) (Reg 'r11)))
           (Instr 'movq (list (select-atm rhs) (Deref 'r11 (* 8 (add1 n))))))]
    [(Prim 'vectorof-set! (list tup e rhs))
     (list (Instr 'movq  (list (select-atm tup) (Reg 'r11)))
           (Instr 'movq  (list (select-atm e) (Reg 'rax)))
           (Instr 'addq  (list (Imm 1) (Reg 'rax)))
           (Instr 'imulq (list (Imm 8) (Reg 'rax)))
           (Instr 'addq  (list (Reg 'rax) (Reg 'r11)))
           (Instr 'movq  (list (select-atm rhs) (Deref 'r11 0))))]))

(define (select-tail e fun-name)
  (match e
    [(Return e) (append (select-expr (Reg 'rax) e)
                        (list (Jmp (symbol-append fun-name '_conclusion))))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim cmp (list a1 a2)) (Goto lt) (Goto lf))
     (list (Instr 'cmpq (list (select-atm a2) (select-atm a1)))
           (JmpIf (get-cc cmp) lt)
           (Jmp lf))]
    [(Seq stmt tail) (append (select-stmt stmt) (select-tail tail fun-name))]
    [(TailCall f args)
     (append (init-args args (take (map Reg (vector->list arg-registers)) (length args)))
             (list (TailJmp f (length args))))]))

(define (init-args arg-s arg-d)
  (match* (arg-s arg-d)
    [('() '()) '()]
    [((cons s arg-s) (cons d arg-d)) (append (list (Instr 'movq (list (select-atm s) (select-atm d))))
                                             (init-args arg-s arg-d))]))

(define (select-instructions-labels lts info fun-name fun-args)
  (cond
    ((dict-empty? lts) (make-immutable-hash))
    (else (define cur-key (car (dict-keys lts)))
          (define tail (if (equal? cur-key (symbol-append fun-name '_start))
                           (append (init-args (take (map Reg (vector->list arg-registers)) (length fun-args))
                                              (map Var (get-fun-args fun-args)))
                                   (select-tail (dict-ref lts cur-key) fun-name))
                           (select-tail (dict-ref lts cur-key) fun-name)))
          (dict-set (select-instructions-labels (dict-remove lts cur-key) info fun-name fun-args)
                    cur-key (Block (dict-remove info 'locals-types) tail)))))

(define (get-num-params ds)
  (match-defs ds '() (λ (v ts t i e ds) (dict-set (get-num-params ds) v (length ts)))))

(define (select-instructions p)
  (match-let [((ProgramDefs info defs) p)]
    (X86ProgramDefs (dict-set* info 'num-root-spills 0 'num-params (get-num-params defs))
                    (rec-defs-new-def defs (λ (v ts t i lts) (Def v '() t (dict-set i 'num-params (length ts))
                                                                  (select-instructions-labels lts i v ts)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; constant-propogation : x86 -> x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (propogate? instr env)
  (or (and (dict-has-key? env instr) (dict-ref env instr))
      (match instr
        [(Imm i) #:when (<= i (expt 2 32)) #t]
        [else #f])))

(define (propogate-to? instr)
  (match instr
    [(Var x) #t]
    [else #f]))

(define (get-imm instr env)
  (match instr
    [(Imm i) i]
    [else (dict-ref env instr)]))

(define (left-shift n m) (arithmetic-shift n (- m)))

(define (propogate-tuah a1 a2 func rfunc env instr two-args?)
  (if (propogate? a1 env)
      (cond
        ((propogate? a2 env)
         (define new-imm (rfunc (get-imm a2 env) (get-imm a1 env)))
         (values (Instr 'movq (list (Imm new-imm) a2))
                 (dict-set env a2 new-imm)))
        (else (values (if two-args? (Instr func (list (Imm (get-imm a1 env)) a2))
                                    (Instr func (list a2))) env)))
      (if (propogate-to? a2)
          (values (if two-args? (Instr func (list a1 a2))
                                (Instr func (list a2))) (dict-set env a2 #f))
          (values (if two-args? (Instr func (list a1 a2))
                                (Instr func (list a2))) env))))

(define (propogate-instr instr env) ;; instr, new env
  (match instr
    [(Callq f a) (values instr (dict-remove env (Reg 'rax)))]
    [(Var x) #:when (propogate? instr env) (values (Imm (get-imm instr env)) env)]
    [(Instr 'movq (list s d)) (if (propogate? s env)
                                  (if (propogate-to? d)
                                      (values (Instr 'movq (list (Imm (get-imm s env)) d))
                                              (dict-set env d (get-imm s env)))
                                      (values (Instr 'movq (list (Imm (get-imm s env)) d)) env))
                                  (if (propogate-to? d)
                                      (values instr (dict-set env d #f))
                                      (values instr env)))]
    [(Instr 'addq  (list a1 a2)) (propogate-tuah a1 a2 'addq  + env instr #t)]
    [(Instr 'subq  (list a1 a2)) (propogate-tuah a1 a2 'subq  - env instr #t)]
    [(Instr 'imulq (list a1 a2)) (propogate-tuah a1 a2 'imulq * env instr #t)]
    [(Instr 'xorq  (list a1 a2)) (propogate-tuah a1 a2 'xorq  bitwise-xor env instr #t)]
    [(Instr 'andq  (list a1 a2)) (propogate-tuah a1 a2 'andq  bitwise-and env instr #t)]
    [(Instr 'sarq  (list a1 a2)) (propogate-tuah a1 a2 'sarq  left-shift env instr #t)]
    [(Instr 'salq  (list a1 a2)) (propogate-tuah a1 a2 'salq  arithmetic-shift env instr #t)]
    [(Instr 'negq  (list a))     (propogate-tuah (Imm 0) a 'negq (λ (a b) (- b a)) env instr #f)]
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

(define (cp-transfer bls fun-name)
  (λ (label pre-env)
    (if (equal? label (symbol-append fun-name '_conclusion))
        pre-env
        (match-let [((Block info instrs) (dict-ref bls label))]
          (define-values (_ env) (propogate-block instrs pre-env))
          env))))

(define (cp-union env1 env2)
  (if (dict-empty? env1)
    env2
    (let ((fst-env1 (car (dict-keys env1))))
      (cond
        ((not (dict-has-key? env2 fst-env1))
         (dict-set (cp-union (dict-remove env1 fst-env1) env2) fst-env1 (dict-ref env1 fst-env1)))
        ((eq? (dict-ref env1 fst-env1) (dict-ref env2 fst-env1))
         (dict-set (cp-union (dict-remove env1 fst-env1) env2) fst-env1 (dict-ref env1 fst-env1)))
        (else (dict-set (cp-union (dict-remove env1 fst-env1) (dict-remove env2 fst-env1)) fst-env1 #f))))))

(define (actually-propogate-blocks bls df-analysis)
  (cond 
    ((dict-empty? bls) (make-immutable-hash))
    (else (define label (car (dict-keys bls)))
          (match-let [((Block info instrs) (dict-ref bls label))]
            (define-values (instrs^ _) (propogate-block instrs (dict-ref df-analysis label)))
            (dict-set (actually-propogate-blocks (dict-remove bls label) df-analysis)
                      label (Block info instrs^))))))

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
    ((dict-empty? bls) void)
    (else (define label (car (dict-keys bls)))
          (match-let ([(Block info instrs) (dict-ref bls label)])
            (define-values (jmp-labels jmpif-labels) (get-jmp-labels instrs))
            (for ([jmp jmp-labels])   (add-directed-edge! cfg label jmp)
                 (add-directed-edge! cfg-only-jmp label jmp))
            (for ([jmp jmpif-labels]) (add-directed-edge! cfg label jmp))
            (when (match (last instrs) [(TailJmp a i) #t] [else #f])
              (add-vertex! cfg label)))
          (build-cf-graph cfg cfg-only-jmp (dict-remove bls label)))))

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

(define (constant-propogation-def fun-name ts t info lts)
  (define cfg (make-multigraph '()))
  (define cfg-only-jmp (make-multigraph '()))
  (build-cf-graph cfg cfg-only-jmp lts)
  (add-vertex! cfg (symbol-append fun-name '_conclusion))
  (define df-analysis (analyze_dataflow cfg (cp-transfer lts fun-name) (make-immutable-hash) cp-union))
  (Def fun-name ts t (dict-set* info 'cf-graph cfg 'cf-graph-only-jmp cfg-only-jmp)
                     (actually-propogate-blocks lts df-analysis)))

(define (constant-propogation p)
  (match-let [((X86ProgramDefs info ds) p)]
    (X86ProgramDefs info (rec-defs-new-def ds constant-propogation-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover-live : x86 -> x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (call? instr) (match instr [(Callq l i) #t] [(IndirectCallq a i) #t] [(TailJmp a i) #t] [else #f]))

(define (locations-read instr)
  (match instr
    [(Instr 'movq (list a1 a2))   (set-union (locations-args a1 #t) (deref-reg-read a2))]
    [(Instr 'movzbq (list a1 a2)) (set-union (locations-args a1 #t) (deref-reg-read a2))]
    [(Instr 'set (list cc a))     (locations-args a #t)]
    [(Instr i (list a))           (locations-args a #t)]
    [(Instr i (list a1 a2))       (set-union (locations-args a1 #t) (locations-args a2 #t))]
    [(Callq label arity)          (get-arg-regs-used arity (vector->list arg-registers))]
    [(IndirectCallq a i)          (set-union (get-arg-regs-used i (vector->list arg-registers)) (locations-args a #t))]
    [(TailJmp a i)                (set-union (get-arg-regs-used i (vector->list arg-registers)) (locations-args a #t))]
    [else (set)]))

(define (locations-write instr)
  (match instr
    [_ #:when (call? instr) caller-save]
    [(Instr 'pushq (list a)) (set)]
    [(Instr i (list a)) (locations-args a #f)]
    [(Instr i (list a1 a2)) (locations-args a2 #f)]    
    [else (set)]))

(define (get-live-after instrs lafter label->live)
  (match instrs
    [`() (cons lafter '())]
    [`(,instr . ,instrs)
     (define ret (get-live-after instrs lafter label->live))
     (define lbefore (get-lbefore instr (car ret) label->live))
     (cons lbefore ret)]))

(define (get-lbefore instr lafter label->live)
  (match instr
    [(Jmp label) (dict-ref label->live label)]
    [(JmpIf cc label) (set-union lafter (dict-ref label->live label))]
    [else (set-union (set-subtract lafter (locations-write instr)) (locations-read instr))]))

(define (deref-reg-read a) (match a [(Deref r i) (set r)] [else (set)]))

(define (locations-args a read?)
  (match a
    [(Var x) (set x)]
    [(Reg r) (set r)]
    [(ByteReg r) (set (byte-reg->full-reg r))]
    [(Deref r i) #:when read? (set r)]
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

(define (get-label->live bls fun-name)
  (dict-set
   (for/list ([bl (dict->list bls)])
     (match-let [((cons label (Block info instrs)) bl)]
       (cons label (if (dict-has-key? info 'live-after-sets)
                       (first (dict-ref info 'live-after-sets))
                       (set)))))
   (symbol-append fun-name '_conclusion) (set 'rax 'rsp)))

(define (analyze-dataflow-transfer bls fun-name)
  (λ (label lafter)
    (if (equal? label (symbol-append fun-name '_conclusion))
        (set 'rax 'rsp)
        (match-let [((Block info instrs) (dict-ref (unbox bls) label))]
          (define-values (lafters block) (uncover-block info instrs (get-label->live (unbox bls) fun-name)))
          (set-box! bls (dict-set (unbox bls) label block))
          (first lafters)))))

(define (uncover-live-def fun-name ts t info bls)
  (define bls-block (box bls))
  (define df-analysis (analyze_dataflow (transpose (dict-ref info 'cf-graph))
                                        (analyze-dataflow-transfer bls-block fun-name) (set) set-union))
  (Def fun-name ts t info (unbox bls-block)))

(define (uncover-live p)
  (match-let [((X86ProgramDefs info defs) p)]
    (X86ProgramDefs info (rec-defs-new-def defs uncover-live-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; eliminate-movqs : x86 -> x86
;; - constant propogation coverts many instructions into movqs that sometimes become redundant. this pass removes those
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (get-symbol instr)
  (match instr
    [(Reg r) r]
    [(Var x) x]
    [else #f]))

(define (deref? e) (match e [(Deref _ _) #t] [else #f]))

(define (remove-movq? instr lafter)
  (match instr
    [(Instr 'movq (list s d)) #:when (and
                                      (not (set-member? lafter (get-symbol d)))
                                      (not (or (deref? s) (deref? d)))) #t]
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

(define (eliminate-movqs-def v ts t info bls)
  (Def v ts t info (dict-map/copy bls (λ (l b) (values l (eliminate-movqs-block b))))))

(define (eliminate-movqs p)
  (match-let [((X86ProgramDefs info defs) p)]
    (X86ProgramDefs info (rec-defs-new-def defs eliminate-movqs-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; build-interference : x86 -> x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (get-var arg)
  (match arg
    [(Var x) x]
    [(Reg x) x]
    [else #f]))

(define (type-vector? t)
  (match t
    [`(Vector . ,_) #t]
    [`(Vectorof . ,_) #t]
    [else #f]))

(define (init-graph ig vars)
  (map (λ (reg) (add-vertex! ig reg))
       (append (set->list caller-save) (set->list callee-save) vars)))

(define (build-interference-rec bls ig mg locals-types)
  (cond
    ((dict-empty? bls) void)
    (else (define label (car (dict-keys bls)))
          (match-let [((Block info instrs) (dict-ref bls label))]
            (add-edges instrs (cdr (dict-ref info 'live-after-sets)) locals-types ig mg))
          (build-interference-rec (dict-remove bls label) ig mg locals-types))))

(define (add-edges instrs live-after-sets locals-types ig mg)
  (cond
    [(null? live-after-sets) '()]
    [else
     (add-edge (car instrs) (car live-after-sets) locals-types ig mg)
     (add-edges (cdr instrs) (cdr live-after-sets) locals-types ig mg)]))

(define (get-move-interference ig live-after s dr)
  (map (λ (d) (map (λ (v) (add-edge! ig d v))
                   (set->list (set-subtract live-after
                                            (set-union (locations-args s #f) (set d))))))
       (set->list (locations-args dr #t))))

(define (add-edge instr live-after locals-types ig mg)
  (match instr
    [(Instr 'movq (list s dr))
     (get-move-interference ig live-after s dr)
     (if (and (get-var s) (get-var dr))
         (add-edge! mg (get-var s) (get-var dr))
         #f)]
    [(Instr 'movzbq (list s dr)) (get-move-interference ig live-after s dr)]
    [else (for* [(d (locations-write instr))
                 (v (set-subtract live-after (set d)))]
            (add-edge! ig d v))])
  (when (call? instr)
    (for* [(d callee-save)
           (v (filter (λ (e) (and (dict-has-key? locals-types e)
                                  (type-vector? (dict-ref locals-types e))))
                      (set->list live-after)))]
      (add-edge! ig d v))))

(define (build-interference-def v ts t info bls)
  (define ig (undirected-graph '()))
  (define mg (undirected-graph '()))
  (init-graph ig (map car (dict-ref info 'locals-types)))
  (init-graph mg (map car (dict-ref info 'locals-types)))
  (build-interference-rec bls ig mg (dict-ref info 'locals-types))
  (remove-vertex! mg 'rax)
  (Def v ts t (dict-set* info 'move_graph mg 'conflicts ig) bls))

(define (build-interference p)
  (match-let [((X86ProgramDefs info defs) p)]
    (X86ProgramDefs info (rec-defs-new-def defs build-interference-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; allocate-registers : x86 -> x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define reg->color-dict (dict-set* (make-immutable-hash) 'rcx 0 'rdx 1 'rsi 2 'rdi 3 'r8 4 'r9 5 'r10 6 'rbx 7
                                   'r12 8 'r13 9 'r14 10 'rax -1 'rsp -2 'rbp -3 'r11 -4 'r15 -5))
(define color->reg-dict (flip-dict reg->color-dict (make-immutable-hash)))
(define (reg->color reg) (dict-ref reg->color-dict reg))
(define (color->reg col) (dict-ref color->reg-dict col))
(define (reg? reg) (dict-has-key? reg->color-dict reg))

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

(define (set-reg-color-mg mg)
  (for [(r (dict-keys reg->color-dict))]
    (when (has-vertex? mg r) (rename-vertex! mg r (cons r (reg->color r))))))

(define (color-graph ig vars mg)
  (define pq (make-pqueue (λ (a b) (if (equal? (set-count (unbox (cdr a))) (set-count (unbox (cdr b))))
                                       ;; check for move related variables and see if color is available
                                       (> (length (get-move-related-colors mg (car a) (unbox (cdr a))))
                                          (length (get-move-related-colors mg (car b) (unbox (cdr b)))))
                                       ;; else max pq by saturation
                                       (> (set-count (unbox (cdr a))) (set-count (unbox (cdr b))))))))
  (define box-list (init-color-list ig vars))
  (define handles (pq-insert-ls pq box-list))
  (set-reg-color-mg mg)
  (dsatur pq ig box-list handles mg))

(define (spill-var c stack-map stack-reg)
  (if (dict-has-key? (cdr stack-map) c)
      (values (dict-ref (cdr stack-map) c) stack-map)
      (let ((spill (Deref stack-reg (* -8 (add1 (car stack-map))))))
        (values spill (cons (add1 (car stack-map)) (dict-set (cdr stack-map) c spill))))))

(define (color->home c t smap rsmap callees)
  (if (<= c 10)
      (let ((r (color->reg c)))
        (values (Reg r) smap rsmap (if (set-member? callee-save r)
                                       (set-add callees (Reg r))
                                       callees)))
      (if (type-vector? t)
          (let-values (((home rsmap) (spill-var c rsmap 'r15)))
            (values home smap rsmap callees))
          (let-values (((home smap) (spill-var c smap 'rbp)))
            (values home smap rsmap callees)))))

(define (colors->homes cs locals-types smap rsmap callees)
  (match cs
    ['() (values callees (car smap) (car rsmap) '())]
    [`(,c . ,cs)
     (define-values (home smap^ rsmap^ callees^) (color->home (cdr c) (dict-ref locals-types (car c)) smap rsmap callees))
     (define-values (callees^^ spilled-s spilled-rs homes) (colors->homes cs locals-types smap^ rsmap^ callees^))
     (values callees^^ spilled-s spilled-rs (dict-set homes (car c) home))]))

(define (assign-arg e homes)
  (match e
    [(Var x) (dict-ref homes x)]
    [else e]))

(define (assign-instr e homes)
  (match e
    [(Instr instr (list arg1 arg2)) (Instr instr (list (assign-arg arg1 homes) (assign-arg arg2 homes)))]
    [(Instr instr (list arg)) (Instr instr (list (assign-arg arg homes)))]
    [(IndirectCallq a i) (IndirectCallq (assign-arg a homes) i)]
    [(TailJmp a i) (TailJmp (assign-arg a homes) i)]
    [else e]))

(define (assign-block e homes)
  (match e
    [(Block info instrs)
     (Block (dict-remove info 'live-after-sets) (for/list ([instr instrs]) (assign-instr instr homes)))]))

(define (allocate-registers-def v ts t info bls)
  (define-values (callees s-spilled rs-spilled homes)
    (colors->homes (color-graph (dict-ref info 'conflicts)
                                (map car (dict-ref info 'locals-types))
                                (dict-ref info 'move_graph))
                   (dict-ref info 'locals-types) (cons 0 '()) (cons 0 '()) (set)))
  (Def v ts t (dict-set* (dict-remove info 'locals-types)
                         'num-root-spills rs-spilled 'stack-space s-spilled 'used_callee callees)
                (dict-map/copy bls (λ (l b) (values l (assign-block b homes))))))

(define (allocate-registers p)
  (match-let [((X86ProgramDefs info defs) p)]
    (X86ProgramDefs info (rec-defs-new-def defs allocate-registers-def))))

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

(define (remove-jumps-def v ts t info bls)
  (define cfgoj (transpose (dict-ref info 'cf-graph-only-jmp)))
  (define removable (filter-map (λ (e)
                                  (if (and (equal? 1 (length (in-neighbors cfgoj e)))
                                           (not (equal? e (symbol-append v '_conclusion))))
                                      (cons e (car (in-neighbors cfgoj e)))
                                      #f))
                                (tsort cfgoj)))
  (Def v ts t info (dict-filter (λ (l b) (not (dict-has-key? removable l)))
                                (remove-jumps-bls bls removable))))

(define (remove-jumps p)
  (match-let [((X86ProgramDefs info defs) p)]
    (X86ProgramDefs info (rec-defs-new-def defs remove-jumps-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; patch-instructions : x86 -> x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (administer-patch-arg1 instr arg1 arg2)
  (list (Instr 'movq (list arg1 (Reg 'rax)))
        (Instr instr (list (Reg 'rax) arg2))))

(define (administer-patch-arg2 instr arg1 arg2)
  (list (Instr 'movq (list arg2 (Reg 'rax)))
        (Instr instr (list arg1 (Reg 'rax)))))

(define (patch-instr e)
  (match e
    [(TailJmp a i) (list (Instr 'movq (list a (Reg 'rax))) (TailJmp (Reg 'rax) i))]
    [(Instr 'movq (list arg1 arg2)) #:when (equal? arg1 arg2) '()]
    [(Instr 'cmpq (list a1 (Imm n))) (administer-patch-arg2 'cmpq a1 (Imm n))]
    [(Instr 'movzbq (list a1 (Deref reg int))) (administer-patch-arg2 'movzbq a1 (Deref reg int))]
    [(Instr instr (list arg1 arg2))
     (match (list arg1 arg2)
       [(list (Deref reg1 int1) (Deref reg2 int2)) (administer-patch-arg1 instr arg1 arg2)]
       [(list (Imm int1) (Deref reg int2)) #:when (> int1 (expt 2 16)) (administer-patch-arg1 instr arg1 arg2)]
       [(list (Deref reg int1) (Imm int2)) #:when (> int2 (expt 2 16)) (administer-patch-arg1 instr arg1 arg2)]
       [else (list e)])]
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

(define (patch-instructions-def v ts t info bls)
  (define kills (make-hash))
  (define blocks (dict-map/copy bls (λ (l b) (define-values (block killable) (patch-block b))
                                      (if killable (dict-set! kills l killable) void)
                                      (values l block))))
  (Def v ts t (dict-set info 'killable-blocks kills) blocks))

(define (patch-instructions p)
  (match-let [((X86ProgramDefs info defs) p)]
    (X86ProgramDefs info (rec-defs-new-def defs patch-instructions-def))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; kill-unused-blocks : x86 -> x86
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
  (cond ((dict-empty? bls) bls)
        (else (define label (car (dict-keys bls)))
              (match-let [((Block info instrs) (dict-ref bls label))]
                (dict-set (replace-jmps-bls (dict-remove bls label) killables)
                          label (Block info (replace-jmps instrs killables)))))))

(define (kill-unused-blocks-def v ts t info bls)
  (define killables (dict-ref info 'killable-blocks))
  (Def v ts t info (dict-filter (λ (l b) (not (dict-has-key? killables l)))
                                (replace-jmps-bls bls killables))))

(define (kill-unused-blocks p)
  (match-let ([(X86ProgramDefs info defs) p])
    (X86ProgramDefs info (rec-defs-new-def defs kill-unused-blocks-def))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; prelude-and-conclusion : x86 -> x86
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (clear-rootstack n)
  (if (zero? n)
      '()
      (cons (Instr 'movq (list (Imm 0) (Deref 'r15 (* 8 (sub1 n)))))
            (clear-rootstack (sub1 n)))))

(define (gen-prelude fun-name used-callee stack-size root-spilled)
  (flatten (list
            (Instr 'pushq (list (Reg 'rbp)))
            (for/list [(cr (set->list used-callee))] (Instr 'pushq (list cr)))
            (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
            (if (positive? stack-size) (Instr 'subq (list (Imm stack-size) (Reg 'rsp))) '())
            (if (equal? fun-name 'main)
                (list (Instr 'movq (list (Imm (expt 2 16)) (Reg 'rdi)))
                      (Instr 'movq (list (Imm (expt 2 16)) (Reg 'rsi)))
                      (Callq 'initialize 2)
                      (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))
                '())
            (clear-rootstack root-spilled)
            (if (positive? root-spilled) (Instr 'addq (list (Imm (* 8 root-spilled)) (Reg 'r15))) '())
            (Jmp (symbol-append fun-name '_start)))))

(define (gen-conclusion used-callee stack-size root-spilled tail-jmp)
  (flatten (list
            (if (positive? root-spilled) (Instr 'subq (list (Imm (* 8 root-spilled)) (Reg 'r15))) '())
            (if (positive? stack-size) (Instr 'addq (list (Imm stack-size) (Reg 'rsp))) '())
            (for/list [(cr (reverse (set->list used-callee)))] (Instr 'popq (list cr)))
            (Instr 'popq (list (Reg 'rbp)))
            (if tail-jmp (IndirectJmp tail-jmp) (Retq)))))

(define (p/c-def fun-name info bls final-bls)
  (define sp (dict-ref info 'stack-space))
  (define rs (dict-ref info 'num-root-spills))
  (define callee (set-add (dict-ref info 'used_callee) (Reg 'r15)))
  (define stack-sz (- (align (+ (* 8 sp) (* 8 (set-count callee))) 16) (* 8 (set-count callee))))
  (dict-append (remove-tail-jmp (dict->list bls) callee stack-sz rs (equal? fun-name 'main))
               (dict-set* final-bls
                          fun-name (Block '() (gen-prelude fun-name callee stack-sz rs))
                          (symbol-append fun-name '_conclusion) (Block '() (gen-conclusion callee stack-sz rs #f)))))

(define (p/c-defs defs final-bls)
  (match defs
    ['() final-bls]
    [(cons (Def v ts t info bls) defs) (p/c-defs defs (p/c-def v info bls final-bls))]))

(define (remove-tail-jmp bls callee stack-sz rs main?)
  (match bls
    ['() '()]
    [(cons (cons label (Block info instrs)) bls)
     (match (last instrs)
       [(TailJmp l i) (cons (cons label (Block info (append (take instrs (sub1 (length instrs)))
                                                            (if main? (list (IndirectCallq l i) (Jmp 'main_conclusion))
                                                                (gen-conclusion callee stack-sz rs l)))))
                            (remove-tail-jmp bls callee stack-sz rs main?))]
       [else (cons (cons label (Block info instrs))
                   (remove-tail-jmp bls callee stack-sz rs main?))])]))

(define (prelude-and-conclusion p)
  (match-let [((X86ProgramDefs info defs) p)]
    (X86Program info (p/c-defs defs '()))))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("eradicate structs" ,eradicate-structs ,interp-Llambda ,type-check-Llambda)
    ("shrink" ,shrink ,interp-Llambda ,type-check-Llambda)
    ;; ("partial evaluate" ,pe-Lvec ,interp-Lvec ,type-check-Lvec)
    ("uniquify" ,uniquify ,interp-Llambda ,type-check-Llambda-has-type)
    ("resolve" ,resolve ,interp-Llambda ,type-check-Llambda)
    ("check bounds" ,check-bounds ,interp-Llambda ,type-check-Llambda)
    ("reveal functions" ,reveal-functions ,interp-Llambda-prime ,type-check-Llambda-typed-vars)
    ("convert assignments" ,convert-assignments ,interp-Llambda-prime ,type-check-Llambda-typed-vars)
    ("closure conversion" ,closure-conversion ,interp-Llambda-prime ,type-check-Llambda)
    ("optimize known calls" ,optimize-known-calls ,interp-Llambda-prime ,type-check-Llambda)
    ("limit functions" ,limit-functions ,interp-Llambda-prime ,type-check-Llambda-has-type)
    ("expose allocation" ,expose-allocation ,interp-Llambda-prime ,type-check-Llambda)
    ("uncover get!" ,uncover-get! ,interp-Llambda-prime ,type-check-Llambda)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Llambda-prime ,type-check-Llambda)
    ("explicate control" ,explicate-control ,interp-Clambda ,type-check-Clambda)
    ("instruction selection" ,select-instructions ,interp-x86-4)
    ("constant propogation" ,constant-propogation ,interp-x86-4)
    ("uncover live" ,uncover-live ,interp-x86-4)
    ("eliminate movqs" ,eliminate-movqs ,interp-x86-4)
    ("build interference" ,build-interference ,interp-x86-4)
    ("allocate registers" ,allocate-registers ,interp-x86-4)
    ("remove jumps" ,remove-jumps ,interp-x86-4)
    ("patch instructions" ,patch-instructions ,interp-x86-4)
    ("kill unused blocks" ,kill-unused-blocks ,interp-x86-4)
    ("prelude-and-coclusion" ,prelude-and-conclusion ,#f)

    ))
