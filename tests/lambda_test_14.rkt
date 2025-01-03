(define (f [x : Integer] [y : Boolean]) : Integer
  (let ([g (lambda: ([z : Integer]) : Integer
             (begin
               (let ([h (lambda: ([a : Integer]) : Integer
                          (+ (if y x 0) (+ a z)))]) 
                 (begin
                   (set! y #f)
                   (set! z 10)
                   (h 32)))))])
    (g x)))

(f 0 #t)
