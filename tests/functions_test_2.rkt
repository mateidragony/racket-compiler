(define (fib [x : Integer]) : Integer 
  (if (< x 2) 1 (+ (fib (- x 1)) (fib (- x 2)))))

(- (fib 10) 47)
