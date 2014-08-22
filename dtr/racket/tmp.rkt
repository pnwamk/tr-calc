#lang typed/racket

(require typed/rackunit)
(require math/matrix)
(require math/array)


(define M (matrix [[1 2 3]
                   [4 5 6]
                   [7 8 9]]))

(submatrix M (:: 0 2) (::))


