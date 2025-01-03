(define (fib-cps [x : Integer] [k : (Integer -> Integer)]) : Integer
  (if (<= x 0) (k 0)
      (if (eq? x 1) (k 1)
          (fib-cps (- x 1) (lambda: ([v : Integer]) : Integer
                             (fib-cps (- x 2) (lambda: ([w : Integer]) : Integer
                                                (k (+ v w)))))))))

(- (fib-cps 10 (lambda: ([x : Integer]) : Integer x)) 13)

