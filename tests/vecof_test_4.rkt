(let ((v1 (make-vector 4 (make-vector 2 42))))
  (vector-ref (vector-ref v1 2) (+ -1 1)))
