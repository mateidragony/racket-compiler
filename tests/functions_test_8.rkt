(define (map [f : (Integer -> Integer)] [v : (Vectorof Integer)]) : (Vectorof Integer)
  (let ((v^ (make-vector (vector-length v) 0)))
    (let ((i 0))
      (begin
        (while (< i (vector-length v))
          (begin
            (vector-set! v^ i (f (vector-ref v i)))
            (set! i (+ i 1))))
        v^))))

(define (add1 [x : Integer]) : Integer
  (+ x 1))

(vector-ref (map add1 (make-vector 10 41)) 9)
