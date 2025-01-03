(define (f) : Integer
  42)

(define (g) : (-> Integer)
  (if #t
      f
      (lambda: () : Integer 0)))

(define (t) : (-> Integer)
  (g))

((t))
