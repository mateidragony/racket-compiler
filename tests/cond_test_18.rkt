(let ([x 1])
  (let ([y 2])
    (let ([z 3])
      (let ([a 11])
        (let ([b 12])
          (let ([c 13])
            (let ([d 21])
              (let ([e 22])
                (let ([f 32])
                  (if (if (<= (read) f)
                          (eq? (+ x (+ y (+ z (+ a (+ b (+ c (+ d (+ e f)))))))) 117)
                          (and #t (or #f (and #f #t))))
                       (+ 100 (- (+ 8 50)))
                       (- 12))
          )))))))))