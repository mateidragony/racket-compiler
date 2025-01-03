(begin
  (let ((v (vector 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
    (let ((i 0))
      (while (< i 100)
        (begin
          (set! v (vector 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
          (set! i (+ i 1))))))
  42)
