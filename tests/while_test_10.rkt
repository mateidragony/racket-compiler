(let ([sum 0])
   (let ([i (read)])
      (begin 
         (while (> i 0)
            (begin 
               (set! sum
                  (+ sum i))
               (set! i
                  (- i 1))))
         (+ 27 sum))))
