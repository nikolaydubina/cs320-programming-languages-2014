#lang plai

;; #1
;;
;; type FLOWER:
;; NOTE: incorrect constructor arguments will cause CONTRACT VIOLATION!
;;
;; sunflower    -> interger interger
;; tulip        -> integer
;; rose         -> string:<either 'red 'yellow 'pink> integer

(define-type FLOWER
    [sunflower (seeds integer?)
               (petals integer?)]
    [tulip  (petals integer?)]
    [rose   (color (lambda (color_value) 
                    (or (equal? color_value 'red) 
                        (equal? color_value 'yellow) 
                        (equal? color_value 'pink ))
            ))
            (petals integer?)]
)

;; #sunflower
;;  pass
(sunflower 1 1)
(sunflower 0 0)
(sunflower -1 -2)
(sunflower -5 2)
;;  none of following should pass. each throws CONTRACT VIOLATION!
;; (sunflower 1 1.3)
;; (sunflower 2.7 5)

;; #tulip
;;  pass
(tulip 1)
(tulip 0)
(tulip -1)
;;  none of following should pass. each throws CONTRACT VIOLATION!
;; (tulip 1.3)

;; #rose
;;  pass
(rose 'red 1)
(rose 'yellow 1)
(rose 'pink 1)
;;  none of following should pass. each throws CONTRACT VIOLATION!
;; (rose 'blue 1)
;; (rose 'finky 1)
;; (rose 2 2)
;; (rose 'red 0.5)
;; (rose 'yellow 0.3)
;; (rose 'pink 2.7)

;; #2
;;
;; has-petals: FLOWER -> integer
;;
;; returns number of petals in flower

( define (has-petals flower)
    (if (FLOWER? flower)
        (cond
          [(sunflower? flower)  (sunflower-petals flower)]
          [(tulip? flower)      (tulip-petals flower)]
          [(rose? flower)       (rose-petals flower)]
        )
        ( error 'has-petals "ERROR: given argument is not of type FLOWER!" )
    )
)

( test (has-petals( sunflower 1 2)) 2) 
( test (has-petals( tulip 3)) 3) 
( test (has-petals( rose 'red 6)) 6)
( test/exn (has-petals 'garbage ) "ERROR: given argument is not of type FLOWER!")

;; #3
;;
;; jealous: FLOWER -> boolean
;;
;; returns true only when FLOWER is 'yellow rose, otherwise false.
;; error is thrown if argument is not of type FLOWER

(define (jealous flower)
    (if (FLOWER? flower)
        (cond
          [(sunflower? flower)  #f]
          [(tulip? flower)      #f]
          [(rose? flower)       (if (equal? (rose-color flower) 'yellow)
                                  #t
                                  #f
                                )]
        )
        ( error 'jealous "ERROR: given argument is not of type FLOWER!" )
    )
)

( test (jealous( rose 'yellow 6)) #t)
( test (jealous( rose 'red 6)) #f)
( test (jealous( sunflower 1 2)) #f) 
( test (jealous( tulip 3)) #f) 
( test/exn (jealous 'garbage ) "ERROR: given argument is not of type FLOWER!")

;; #4
;;
;; all-even?: list of integers -> boolean
;;
;; returns true if all integers in the list are even, otherwise false
;; error thrown if either:
;; - argument is not type of list
;; - element in list is not type of integer

(define (all-even? q)
    (if (list? q)
        (if (not (null? q))
            (if (integer? (car q))
                (if (not (null? (cdr q)))
                    (and (even? (car q)) (all-even? (cdr q)))
                    (even? (car q))
                )
                ( error 'all-even? "ERROR: element in list is not of type integer!" )
            )
            #f
        )
        ( error 'all-even? "ERROR: given argument is not of type list!" )
    )
)

(test (all-even? '(1 3 5)) #f)
(test (all-even? '(2 4 6)) #t)
(test (all-even? '(1 2 4)) #f)
(test (all-even? '(2 1 4)) #f)
(test (all-even? '(2 4 1)) #f)
(test (all-even? empty) #f)

( test/exn (all-even? 'garbage )     "ERROR: given argument is not of type list!")
( test/exn (all-even? '(4 2 0.5) )   "ERROR: element in list is not of type integer!")
( test/exn (all-even? '(8 0.1 2) )   "ERROR: element in list is not of type integer!")
( test/exn (all-even? '(0.8 1 2) )   "ERROR: element in list is not of type integer!")

;; #5
;;
;; merge-lists: list<number> list<number> -> list<number>
;;
;; merges two lists of numbers, each sorted by ascending order into
;; one sorted list by ascending order

(define (merge-lists l1 l2)
    (if (and (list? l1) (list? l2))
        (cond
            [(not (or (null? l1) (null? l2)))
                (if (and (number? (car l1)) (number? (car l2)))
                    (if (< (car l1) (car l2))
                        (cons (car l1) (merge-lists (cdr l1) l2))
                        (cons (car l2) (merge-lists l1 (cdr l2)))
                    )
                    ( error 'merge-lists "ERROR: non-number element in list found!" )
                )]
            [(and (null? l1) (not (null? l2))) l2]
            [(and (null? l2) (not (null? l1))) l1]
            [(and (null? l2) (null? l1)) '()]
        )
        ( error 'merge-lists "ERROR: given arguments is not of type list!" )
    )
)

(test (merge-lists '(1 3 5) '(2 4 6))   '(1 2 3 4 5 6))
(test (merge-lists '(1 3 5) '(0))       '(0 1 3 5))
(test (merge-lists '(1 3 5) '(6))       '(1 3 5 6))
(test (merge-lists '(0) '(2 4 6))       '(0 2 4 6))
(test (merge-lists '(7) '(2 4 6))       '(2 4 6 7))
(test (merge-lists '(1 3 5) '())        '(1 3 5))
(test (merge-lists '() '(2 4 6))        '(2 4 6))
(test (merge-lists '() '())             '())

( test/exn (merge-lists '(3 2) 't2 )        "ERROR: given arguments is not of type list!")
( test/exn (merge-lists 't1 '(1 1) )        "ERROR: given arguments is not of type list!")
( test/exn (merge-lists '(1 'x) '(1 2) )    "ERROR: non-number element in list found!")
( test/exn (merge-lists '(1 3) '(1 'x) )    "ERROR: non-number element in list found!")
