(let ((v (vector 0)))
  (begin
    (set! v (vector 1 42))
    (+ 40 (vector-length v))))
