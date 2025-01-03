(define (f) : (-> Integer)
  (let ((x 0))
    (let ((g (lambda: () : Integer x)))
      (begin
        (set! x 42)
        g))))

((f))
