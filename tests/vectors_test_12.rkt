(let ((v (vector #t 42 0)))
  (if (vector-ref v 0)
      (vector-ref v 1)
      (vector-ref v 2)))
