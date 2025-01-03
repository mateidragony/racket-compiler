(struct point ([x : Integer] [y : Integer]) #:mutable)
(struct ptpt ([pt1 : point] [pt2 : point]) #:mutable)

(point-x (ptpt-pt1 (ptpt (point 42 42) (point 42 42))))
