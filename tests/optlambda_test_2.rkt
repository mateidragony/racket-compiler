(define (inc [x : Integer]) : Integer
  (+ x 1))

(let ((y (read)))
  (let ((f (if (eq? (read) 0)
               inc
               (lambda: ([x : Integer]) : Integer (- x y)))))
    (f 41)))
