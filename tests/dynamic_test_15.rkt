(define (add1 x)
  (+ x 1))

(define (sub1 x) 
  (+ x 1))

(define (ten-reads)
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

(define (do-thing f1 f2 x)
  (if (eq? 0 (read))
      (f1 x)
      (f2 x)))

(do-thing add1 sub1 (ten-reads))
