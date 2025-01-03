(let ((v1 (vector 10 10)))
  (let ((v2 (vector 30 30)))
    (let ((v3 (vector 2 2)))
      (+ (vector-ref v1 0) (+ (vector-ref v2 0) (vector-ref v3 0))))))
