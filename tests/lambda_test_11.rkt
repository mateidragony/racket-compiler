(define (test [x : Integer] [f : (-> Integer)] [g : (Integer -> Integer)] [h : (Integer Integer -> Integer)]
              [i : ((Integer -> Integer) (Integer Integer -> Integer) -> (Integer -> Integer))]) : Integer
  (+ (f) (+ (g x) (+ (h x x) ((i g h) x)))))

(test 7 (lambda: () : Integer 0)
        (lambda: ([x : Integer]) : Integer x)
        (lambda: ([x : Integer] [y : Integer]) : Integer (+ x y))
        (lambda: ([f : (Integer -> Integer)] [g : (Integer Integer -> Integer)]) : (Integer -> Integer)
          (lambda: ([x : Integer]) : Integer (+ (f x) (g x x)))))
