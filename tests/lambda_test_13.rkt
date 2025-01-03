(define (g [x : Integer]) : Integer
  (let ((f (lambda: ([a : Integer]) : Integer (+ a x))))
    (begin
      (set! x 10)
      (f 32))))

(g 29324)
