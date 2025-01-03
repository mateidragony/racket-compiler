(define (map f v)
    (vector (f (vector-ref v 0)) (f (vector-ref v 1))))

(define (inc x)
  (+ x 1))

(vector-ref (map inc (vector 0 41)) 1)
