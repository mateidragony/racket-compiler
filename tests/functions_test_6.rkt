(define (map [f : (Integer -> Integer)] [v : (Vector Integer Integer)])
        : (Vector Integer Integer)
    (vector (f (vector-ref v 0)) (f (vector-ref v 1))))

(define (inc [x : Integer]) : Integer
  (+ x 1))

(vector-ref (map inc (vector 0 41)) 1)