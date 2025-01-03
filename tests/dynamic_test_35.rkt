(define (f x y)
  (let ([g (lambda (z) 
             (begin
               (let ([h (lambda (a) 
                          (+ (if y x 0) (+ a z)))]) 
                 (begin
                   (set! y #f)
                   (set! z 10)
                   (h 32)))))])
    (g x)))

(f 0 #t)
