(let ((x (read)))
    (let ((y (read)))
        (let ((z (read)))
            (let ((w (+ z z)))
                (+ w (if (eq? z 0)
                    x
                    y))))))