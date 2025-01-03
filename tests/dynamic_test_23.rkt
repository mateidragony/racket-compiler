(define (doubleid x) 
  ((lambda (x) x) x))
(doubleid 42)
