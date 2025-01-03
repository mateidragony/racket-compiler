(define (f) 
  (let ((g (lambda (x)
             (let ((h (lambda () x)))
               (begin
                 (set! x 42)
                 h)))))
    g))

(((f) 42))
