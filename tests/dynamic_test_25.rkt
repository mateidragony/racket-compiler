(define (f x)
  (let ((y 4))
    (lambda (x)
      (+ x (+ y 4)))))

(let ((g (f 5)))
  (let ((h (f 3)))
    (+ (g 11) (h 15))))
