(define (f) : (Integer -> (-> Integer))
  (let ((g (lambda: ([x : Integer]) : (-> Integer)
             (let ((h (lambda: () : Integer x)))
               (begin
                 (set! x 42)
                 h)))))
    g))

(((f) 42))
