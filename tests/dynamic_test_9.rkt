(define (fib x acc1 acc2)
  (if (< x 2) acc1
      (fib (- x 1) (+ acc1 acc2) acc1)))

(- (fib 10 1 1) 47)
