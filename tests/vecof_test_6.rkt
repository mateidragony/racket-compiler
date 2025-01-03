(let ((A (make-vector 3 14)))
  (let ((B (make-vector 3 1)))
    (let ((i 0))
      (let ((prod 0))
        (begin
          (while (< i (vector-length A))
            (begin
              (set! prod (+ prod (* (vector-ref A i)
                                    (vector-ref B i))))
              (set! i (+ i 1))))
          prod)))))
