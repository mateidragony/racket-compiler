(let ([x 2])
    (let ([y 0])
        (+ y (+ x (begin (set! x 40) x)))))