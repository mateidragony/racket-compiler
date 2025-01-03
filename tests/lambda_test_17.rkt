(define (add-alot [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] [f : Integer] [g : Integer] [h : Integer])
        : Integer (+ a (+ b (+ c (+ d (+ e (+ f (+ g h))))))))

(let ((sub-alot (lambda: ([a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] [f : Integer] [g : Integer] [h : Integer])
                         : Integer (- a (- b (- c (- d (- e (- f (- g h))))))))))
  (+ 35 (+ (add-alot 1 1 1 1 1 1 1 1) (sub-alot 0 1 1 1 1 1 1 1))))
