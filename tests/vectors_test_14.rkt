(let ((v1 (vector 0 0 0 0 0 0 0 0 0 0)))
  (let ((v2 (vector 21 21 21 21 21 21 21 21 21 21)))
    (let ((v3 (vector 21 21 21 21 21 21 21 21 21 21)))
      (+ (vector-ref v1 0) (+ (vector-ref v2 0) (vector-ref v3 0))))))
