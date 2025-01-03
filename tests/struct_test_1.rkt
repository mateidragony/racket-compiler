(struct point ([x : Integer] [y : Integer]) #:mutable)

(let ([pt1 (point 7 42)])
  (let ([pt2 (point 4 3)])
    (+ (- (point-x pt1) (point-x pt2))
       (- (point-y pt1) (point-y pt2)))))
