(define (add [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] [f : Integer]
             [g : Integer] [h : Integer] [i : Integer]) : Integer
  (+ a (+ b (+ c (+ d (+ e (+ f (+ g (+ h i)))))))))

(- (add 1 2 3 4 5 6 7 8 9) 3)
