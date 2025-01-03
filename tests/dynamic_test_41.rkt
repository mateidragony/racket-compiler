(define (fib-cps x k) 
  (if (<= x 0) (k 0)
      (if (eq? x 1) (k 1)
          (fib-cps (- x 1) (lambda (v) 
                             (fib-cps (- x 2) (lambda (w) 
                                                (k (+ v w)))))))))

(let ((fib (fib-cps (read) (lambda: (x) x))))
  42)
