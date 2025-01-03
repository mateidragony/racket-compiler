(define (mult m n) 
  (if (eq? 0 m) 0 (+ n (mult (- m 1) n))))

(define (fact n) 
  (if (eq? 0 n) 1 (mult n (fact (- n 1)))))

(- (fact 5) 78)
