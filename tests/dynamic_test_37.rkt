(let ((f (lambda (x) 
           (let ((g (lambda ()  x)))
             (begin
               (set! x 42)
               g)))))
  ((f 0)))
