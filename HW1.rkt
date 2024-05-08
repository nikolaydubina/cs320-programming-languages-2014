#lang plai

;; #1
;; yen->won: number -> number
;;
;; converts yen to won. yen should be >= 0

(define (yen->won yen)
    (* yen 10)
)

(test (yen->won 1) 10)
(test (yen->won 10) 100)
(test (yen->won 0.5) 5)
(test (yen->won 0.001) 0.01)
(test (yen->won 0.1) 1)
(test (yen->won 0) 0)

;; #2
;; volume-cube: number -> number
;;
;; calculates volume of cube based on its dimensions

(define (volume-cube a)
    (* a a a)  
)

(test  (volume-cube 0) 0)
(test  (volume-cube 1) 1)
(test  (volume-cube 3) 27)
(test  (volume-cube 2.5) 15.625)
(test  (volume-cube 0.1) 0.001)

;; #3
;; area-cube: number -> number
;;
;; computes total area of a surface of a cube with given dimensions

(define (area-cube a)
    (* 6 (* a a))  
)

(test (area-cube 1) 6)
(test (area-cube 0.5) 1.5)
(test (area-cube 3) 54)
(test (area-cube 0) 0)

;; #4
;; tax: number -> number
;;
;; assumes tax-rate as follows: for <=250           -> 0%
;;                              for >250 and <=500  -> 15%
;;                              for >500            -> 30%

(define (tax gross)
    (if (<= gross 250) 
        0
        (if (<= gross 500) 
            (* 0.15 gross)
            (* 0.30 gross)
        )
    )  
)

(test (tax 0) 0)
(test (tax 0.5) 0)
(test (tax 250) 0)
(test (tax 249.5) 0)
(test (tax 250.1) 37.515)
(test (tax 260) 39.0)
(test (tax 499.99) 74.9985)
(test (tax 500) 75)
(test (tax 500.1) 150.03)
(test (tax 502) 150.6)
(test (tax 100000) 30000.0)

;; #5
;; netpay: number -> number
;;
;; computes netpay as gross-pay minus tax from number of hours worked.
;; aussuming hourly payrate is 11

(define (netpay hours)
    (- (* 11 hours) (tax (* 11 hours)))
)

(test (netpay 0) 0)
(test (netpay 10) 110)
(test (netpay 15) 165)
(test (netpay 22) 242)
(test (netpay 23) 215.05)
(test (netpay 45) 420.75)
(test (netpay 46) 354.2)
(test (netpay 50) 385.0)
