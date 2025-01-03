(define (f)
  (let ((x 0))
    (let ((g (lambda ()  x)))
      (begin
        (set! x 42)
        g))))

((f))
