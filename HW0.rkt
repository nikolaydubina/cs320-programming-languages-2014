#lang plai

(define (check_1 a b c)
  (* a b c)
)

(test (check_1 3 3 3) 27)