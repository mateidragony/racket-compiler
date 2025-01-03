(let ([y 2])
    (let ([x 0])
        (begin
            (while (< x 4)
                (begin
                    (set! x (+ x 1))
                    (set! y (+ 10 y))))
            y)))