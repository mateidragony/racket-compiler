(define (f) : Integer
  42)

(define (g) : Integer
  0)

(let ((test f))
  (begin
    (if (eq? (read) 0)
        (set! test (lambda: () : Integer 42))
        (set! test g))
    (test)))
