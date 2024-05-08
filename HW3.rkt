;; HW3
;; Mykola Dubyna
;; 20121103

;; NOTE:    often tests are constructed as follows:
;;          wrapped into lambda test of function check each element of list
;;          each element of list: 1st value is argument, 2nd desired return value


#lang plai

;; <WAE> ::= <num>
;;        | {+ <WAE> <WAE>}
;;        | {- <WAE> <WAE>}
;;        | {with {<id> <WAE>} <WAE>}
;;        | <id>

(define-type WAE
    [num (n number?)]
    [add (lhs WAE?) (rhs WAE?)]
    [sub (lhs WAE?) (rhs WAE?)]
    [with   (name symbol?)
            (named-expr WAE?)
            (body WAE?)]
    [id (name symbol?)]
)

;; parser
(define (parse sexp)
    (match sexp
        [(? number?) (num sexp)]
        [(list '+ l r) (add (parse l) (parse r))]
        [(list '- l r) (sub (parse l) (parse r))]
        [(list 'with (list x i) b) (with x (parse i) (parse b))]
        [(? symbol?) (id sexp)]
        [else (error 'parse "bad syntax: ~a" sexp)]
    )
)

;; parser tests
(for-each (lambda (q) (test (parse (first q)) (second q)))
    (list
        (list '42           (num 42))
        (list 'x            (id 'x))
        (list '{ + 2 3 }    (add (num 2) (num 3)))
        (list '{ - 2 3 }    (sub (num 2) (num 3)))
        (list '{ - x y }    (sub (id 'x) (id 'y)))
        (list '{ with { x 5 } { + 8 { - x 2 }}} (with 'x (num 5) (add (num 8) (sub (id 'x) (num 2)))) )
    )
)

;; #1
;;
;; free-ids : WAE → list-of-sym 
;;
;; returns a list which contains a symbol for each free indentifier in WAE
;; without sorting - keep an eye on order!
;; with repetitions

(define (free-ids-repeat q)
    (cond 
        [(num? q)   '()]
        [(id? q)    (list (id-name q))]
        [(add? q)
            (append 
                (free-ids-repeat (add-lhs q))
                (free-ids-repeat (add-rhs q))
            )
        ]
        [(sub? q)
            (append 
                (free-ids-repeat (sub-lhs q))
                (free-ids-repeat (sub-rhs q))
            )
        ]
        [(with? q)
            (append
                (free-ids-repeat (with-named-expr q))
                (filter (lambda (t) (not (equal? t (with-name q)))) 
                    (free-ids-repeat (with-body q))
                )
            )
        ]
        [else (error 'free-ids-repeat "ERROR: type/constructor of argument is not supported")]
    )
)

;; following tests are sensetive to implementation!
;; because of return values (lits) are not sorted and with duplicates
(test/exn (free-ids-repeat 2) "ERROR: type/constructor of argument is not supported")

(for-each   (lambda (q) (test (free-ids-repeat (parse (first q))) (second q)))
    (list 
        (list '42                                                   '() )
        (list 'x                                                    '(x) )
        (list '{ + x y }                                            '(x y) )
        (list '{ - x y }                                            '(x y) )
        (list '{ with { x x }  { + x x }}                           '(x) )
        (list '{ with { x { + 1 2 }}  { + x x }}                    '() )
        (list '{ with { x { + 1 2 }}  { + x y }}                    '(y) )
        (list '{ with { x { + 1 y }}  { + x y }}                    '(y y) )
        (list '{ with { x { + y z }}  { + x y }}                    '(y z y) )
        (list '{ with { x { - y z }}  { + x y }}                    '(y z y) )
        (list '{ with { x { + x x }}  { + x y }}                    '(x x y) )
        (list '{ with { x x }  { with { x x } { - x x } } }         '(x) )
        (list '{ with { x x }  { with { x x } { - x x } } }         '(x) )
        (list '{ with { x x }  { with { x { + c d } } { - a b } } } '(x c d a b) )
    )
)

;; free-ids : WAE → list-of-sym 
;;
;; return list which contains a symbol for each free indentifier in WAE
;; sorted by function "sumbol<? : symbol symbol -> boolean"
;; removed duplicates

(define (symbol<? a b) (string<? (symbol->string a) (symbol->string b)))

(define (free-ids q)
    (sort
        (remove-duplicates (free-ids-repeat q))
        symbol<?
    )
)

(test/exn (free-ids 2) "ERROR: type/constructor of argument is not supported")

(for-each   (lambda (q) (test (free-ids (parse (first q))) (second q)))
    (list
        (list '{ + a b }                                    '(a b) )
        (list '{ + b a }                                    '(a b) )
        (list '{ - b a }                                    '(a b) )
        (list '{ + c { + b { + a d }}}                      '(a b c d) )
        (list '{ + a { + a { + a a }}}                      '(a) )
        (list '{ + a { + b { + a b }}}                      '(a b) )
        (list '{ + a { + b { + c c }}}                      '(a b c) )
        (list '42                                           '() )
        (list 'a                                            '(a) )
        (list '{ with { a a }  { + a a }}                   '(a) )
        (list '{ with { a { + 1 2 }}  { + a a }}            '() )
        (list '{ with { a { + 1 2 }}  { + a b }}            '(b) )
        (list '{ with { a { + 1 b }}  { + a b }}            '(b) )
        (list '{ with { a { + b c }}  { + a b }}            '(b c) )
        (list '{ with { a { - b c }}  { + a b }}            '(b c) )
        (list '{ with { a { + a a }}  { + a b }}            '(a b) )
        (list '{ with { a a }  { with { a a } { - a a } } } '(a) )
        (list '{ with { a c }  { with { a a } { - a b } } } '(b c) )
        (list '{ with { a c }  { with { a b } { - a d } } } '(b c d) )
    )
)

;; #2
;;
;; binding-ids-repeat: WAE → list-of-sym
;;
;; returns a list which contains a symbol for each of binding identifiers
;; without sorting - keep an eye on order!
;; with repetitions

(define (binding-ids-repeat q)
    (cond 
        [(num? q)   '()]
        [(id? q)    '()]
        [(add? q)
            (append 
                (binding-ids-repeat (add-lhs q))
                (binding-ids-repeat (add-rhs q))
            )
        ]
        [(sub? q)
            (append 
                (binding-ids-repeat (sub-lhs q))
                (binding-ids-repeat (sub-rhs q))
            )
        ]
        [(with? q)
            (append
                (list (with-name q))
                (binding-ids-repeat (with-named-expr q))
                (binding-ids-repeat (with-body q))
            )
        ]
        [else (error 'binding-ids-repeat "ERROR: type/constructor of argument is not supported")]
    )
)

;; binding-ids : WAE → list-of-sym
;;
;; returns a list which contains a symbol for each of binding identifiers
;; sorted by function "sumbol<? : symbol symbol -> boolean"
;; removed duplicates

(define (binding-ids q)
    (sort
        (remove-duplicates (binding-ids-repeat q))
        symbol<?
    )
)

(test/exn (binding-ids 2) "ERROR: type/constructor of argument is not supported")

(for-each   (lambda (q) (test (binding-ids (parse (first q))) (second q)))
    (list
        (list '{ + a b }                                    '() )
        (list '{ - b a }                                    '() )
        (list '{ + c { + b { + a d }}}                      '() )
        (list '42                                           '() )
        (list 'a                                            '() )
        (list '{ with { a a }  { + a a }}                   '(a) )
        (list '{ with { a { + 1 2 }}  { + a a }}            '(a) )
        (list '{ with { a { + 1 2 }}  { + a b }}            '(a) )
        (list '{ with { a { + 1 b }}  { + a b }}            '(a) )
        (list '{ with { a { + b c }}  { + a b }}            '(a) )
        (list '{ with { a { - b c }}  { + a b }}            '(a) )
        (list '{ with { a { + a a }}  { + a b }}            '(a) )
        (list '{ with { a a }  { with { a a } { - a a } } } '(a) )
        (list '{ with { a c }  { with { a a } { - a b } } } '(a) )
        (list '{ with { a c }  { with { a b } { - a d } } } '(a) )
        (list '{ with { a a }  { with { c d } { - b b } } } '(a c) )
        (list '{ with { b c }  { with { a b } { - a d } } } '(a b) )
        (list '{ with { b c }  { with { a b } { - a d } } } '(a b) )
        (list '{ with { b c }  { with { a { with { c a } { + c c } } } { - a { with { d c } { - d d } } } } } '(a b c d) )
        (list '{ with { d a }  { with { c { with { a c } { + a a } } } { - c { with { b a } { - b b } } } } } '(a b c d) )
    )
)

;; #3
;;
;; bound-ids-repeat: WAE → list-of-sym
;;
;; returns a list which contains a symbol for each of bound identifiers
;; without sorting - keep an eye on order!
;; with repetitions

(define (bound-ids-repeat q b)
    (cond 
        [(num? q)   '()]
        [(id? q)    (if (equal? (member (id-name q) b) #f)
                        '()
                        (list (id-name q))
                    )
        ]
        [(add? q)
            (append 
                (bound-ids-repeat (add-lhs q) b)
                (bound-ids-repeat (add-rhs q) b)
            )
        ]
        [(sub? q)
            (append 
                (bound-ids-repeat (sub-lhs q) b)
                (bound-ids-repeat (sub-rhs q) b)
            )
        ]
        [(with? q)
            (append
                (bound-ids-repeat (with-body q) (append b (list (with-name q))) )
                (bound-ids-repeat (with-named-expr q) b)
            )
        ]
        [else (error 'bound-ids-repeat "ERROR: type/constructor of argument is not supported")]
    )
)

;; bound-ids : WAE → list-of-sym
;;
;; returns a list which contains a symbol for each of bound identifiers
;; sorted by function "sumbol<? : symbol symbol -> boolean"
;; removed duplicates

(define (bound-ids q)
    (sort
        (remove-duplicates (bound-ids-repeat q empty ) )
        symbol<?
    )
)

(test/exn (bound-ids 2) "ERROR: type/constructor of argument is not supported")

(for-each   (lambda (q) (test (bound-ids (parse (first q))) (second q)))
    (list
        (list '{ + a b }                                    '() )
        (list '{ - b a }                                    '() )
        (list '{ + c { + b { + a d }}}                      '() )
        (list '42                                           '() )
        (list 'a                                            '() )
        (list '{ with { a a }  { + a a }}                   '(a) )
        (list '{ with { a { + 1 2 }}  { + a a }}            '(a) )
        (list '{ with { a { + 1 2 }}  { + a b }}            '(a) )
        (list '{ with { a { + 1 b }}  { + a b }}            '(a) )
        (list '{ with { a { + b c }}  { + a b }}            '(a) )
        (list '{ with { a { - b c }}  { + a b }}            '(a) )
        (list '{ with { a { + a a }}  { + a b }}            '(a) )
        (list '{ with { a a }  { with { a a } { - a a } } } '(a) )
        (list '{ with { a a }  { with { a a } { - b b } } } '(a) )
        (list '{ with { a a }  { with { c d } { - b b } } } '() )
        (list '{ with { a c }  { with { a a } { - a b } } } '(a) )
        (list '{ with { a c }  { with { a b } { - a d } } } '(a) )
        (list '{ with { a c }  { with { a b } { - c b } } } '() )
        (list '{ with { b c }  { with { a d } { - a b } } } '(a b) )
        (list '{ with { b c }  { with { a { with { c a } { + c c } } } { - a { with { d c } { - d d } } } } } '(a c d) )
        (list '{ with { d a }  { with { c { with { a c } { + a a } } } { - c { with { b a } { - b b } } } } } '(a b c) )
    )
)

