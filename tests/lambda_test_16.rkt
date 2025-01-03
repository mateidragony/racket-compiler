(let ((f (lambda: ([x : Integer]) : (-> Integer)
           (let ((g (lambda: () : Integer x)))
             (begin
               (set! x 42)
               g)))))
  ((f 0)))
