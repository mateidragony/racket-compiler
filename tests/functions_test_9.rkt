(define (add1 [x : Integer]) : Integer
  (+ x 1))

(define (sub1 [x : Integer]) : Integer
  (+ x 1))

(define (ten-reads) : Integer
  (begin
    (read)
    (read)
    (read)
    (read)
    (read)
    (read)
    (read)
    (read)
    (read)
    (read)))

(define (do-thing [f1 : (Integer -> Integer)] [f2 : (Integer -> Integer)] [x : Integer]) : Integer
  (if (eq? 0 (read))
      (f1 x)
      (f2 x)))

(do-thing add1 sub1 (ten-reads))
