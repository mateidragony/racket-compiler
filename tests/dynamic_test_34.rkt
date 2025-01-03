(define (g x)
  (let ((f (lambda (a)  (+ a x))))
    (begin
      (set! x 10)
      (f 32))))

(g 29324)
