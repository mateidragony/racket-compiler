(if #t
    (+ 42 (- 214 (let ([a 42])
        (let ([b a])
            (- 65537 (+ b 65537))))))
    (+ 42 (- 214 (let ([a 42])
        (let ([b a])
            (- 65537 (+ b 65537)))))))
