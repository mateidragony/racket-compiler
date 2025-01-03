(let ((v (vector 0)))
  (let ((i 0))
    (let ((sum 0))
      (begin
        (while (< i 42)
          (begin
            (set! v (vector 1 v))
            (set! i (+ 1 i))))
        42))))
