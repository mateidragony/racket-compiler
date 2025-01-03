(define (cons a b)
  (vector a b))

(define (car ls)
  (vector-ref ls 0))

(define (cdr ls)
  (vector-ref ls 1))

(define (null? v)
  (eq? (vector-length v) 0))

(define (length ls)
  (if (null? ls)
      0
      (+ 1 (length (cdr ls)))))

(let ((null (vector)))
  (+ 38 (length (cons 0 (cons 1 (cons 2 (cons 3 null)))))))
