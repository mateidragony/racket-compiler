(let ((v (vector 0)))
  (begin
    (begin
      (vector-set! v 0 42)
      0)
    (vector-ref v 0)))
