(define (f) : Integer 42)

(define (rec1 [x : Integer]) : (-> Integer)
  (if (eq? x 0)
      f
      (rec2 (- x 1))))

(define (rec2 [x : Integer]) : (-> Integer)
  (if (eq? x 0)
      (lambda: () : Integer 42)
      (rec1 (- x 1))))

((rec1 10))
