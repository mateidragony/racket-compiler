(define (add-alot a b c d e f g h)
  (+ a (+ b (+ c (+ d (+ e (+ f (+ g h))))))))

(let ((sub-alot (lambda (a b c d e f g h)
                  (- a (- b (- c (- d (- e (- f (- g h))))))))))
  (+ 35 (+ (add-alot 1 1 1 1 1 1 1 1) (sub-alot 0 1 1 1 1 1 1 1))))
