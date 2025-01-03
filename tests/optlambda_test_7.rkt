(let ([add1 (lambda: ([x : Integer]) : Integer x)])
  (begin
    (set! add1 (lambda: ([x : Integer]) : Integer (+ 1 x)))
    (add1 41)))
