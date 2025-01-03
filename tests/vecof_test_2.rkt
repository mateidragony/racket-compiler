(let ((v1 (make-vector 40 9)))
  (let ((v2 (vector 9 9)))
    (begin
      (vector-set! v1 0 0)
      (vector-set! v2 0 0)
      (+ (vector-length v1) (+ (vector-length v2) (+ (vector-ref v1 0) (vector-ref v2 0)))))))
