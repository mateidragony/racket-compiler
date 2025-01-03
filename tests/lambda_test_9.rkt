(define (f) : (-> Integer)
  (let ((x 0))
    (lambda: () : Integer
      (begin
        (set! x 42)
        x))))

((f))
