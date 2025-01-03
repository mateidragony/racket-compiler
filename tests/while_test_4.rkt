(let ([x 10])
    (begin
        (set! x 42)
        (+ 4 5)
        (if (< (read) x)
            999
            (+ 1 2))
        x))