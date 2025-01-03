(define (null? v)
  (eq? (vector-length v) 0))

(let ((null (vector)))
  (if (null? null)
      42
      0))
