(begin
    (let ((x 10))
        (+ x (read)))
    (let ((x (read)))
        (+ x 10))
    (let ((x (read)))
        (+ x (read)))
    (read))