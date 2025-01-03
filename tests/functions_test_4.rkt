(define (mult [m : Integer] [n : Integer]) : Integer
  (if (eq? 0 m) 0 (+ n (mult (- m 1) n))))

(define (fact [n : Integer]) : Integer
  (if (eq? 0 n) 1 (mult n (fact (- n 1)))))

(- (fact 5) 78)