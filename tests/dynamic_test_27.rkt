(define (fact-cps x k) 
  (if (eq? x 0)
      (k 1)
      (fact-cps (- x 1) (lambda (v) (* x (k v))))))

(- (fact-cps 5 (lambda (x)  x)) 78)
