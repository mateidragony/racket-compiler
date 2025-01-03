(define (fact-cps [x : Integer] [k : (Integer -> Integer)]) : Integer
  (if (eq? x 0)
      (k 1)
      (fact-cps (- x 1) (lambda: ([v : Integer]) : Integer (* x (k v))))))

(- (fact-cps 5 (lambda: ([x : Integer]) : Integer x)) 78)
