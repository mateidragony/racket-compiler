(define (f) 
  (let ((x 0))
    (lambda () 
      (begin
        (set! x 42)
        x))))

((f))
