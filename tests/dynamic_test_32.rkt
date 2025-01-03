(define (test x f g h i)
  (+ (f) (+ (g x) (+ (h x x) ((i g h) x)))))

(test 7 (lambda () 0)
        (lambda (x)  x)
        (lambda (x y) (+ x y))
        (lambda (f g) 
          (lambda (x) (+ (f x) (g x x)))))
