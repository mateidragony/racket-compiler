(define (is-odd? x) 
  (if (eq? x 0) #f (is-even? (- x 1))))

(define (is-even? x)
  (if (eq? x 0) #t (is-odd? (- x 1))))

(if (is-odd? 13) 42 0)
