#lang plai

;; HW4
;; Mykola Dubyna
;; 20121103

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

;; MUWAE abstract syntax trees
(define-type MUWAE
  [num      (num  (listof number?))]
  [add      (left MUWAE?) (right MUWAE?)]
  [sub      (left MUWAE?) (right MUWAE?)]
  [sqrtp    (arg  MUWAE?)]
  [with     (name symbol?) (init MUWAE?) (body MUWAE?)]
  [id       (name symbol?)])

;; parse-sexpr : sexpr -> MUWAE
;; to convert s-expressions into MUWAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?)    (num (list sexp))]
    [(list '+ l r)  (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r)  (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'sqrt x) (sqrtp (parse-sexpr x))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?)    (id sexp)]
    [else           (error 'parse "bad syntax: ~a" sexp)]))

;; parses a string containing a MUWAE expression to a MUWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  (type-case MUWAE expr
    [num (n)    (num n)]
    [add (l r)  (add (subst l from to) (subst r from to))]
    [sub (l r)  (sub (subst l from to) (subst r from to))]
    [sqrtp (x)  (sqrtp (subst x from to))]
    [id (name)  (if (symbol=? name from) (num to) expr)]
    [with (bound-id named-expr bound-body)
          (with bound-id
                (subst named-expr from to)
                (if (symbol=? bound-id from)
                    bound-body
                    (subst bound-body from to)))]))

;; sqrt+ : listof number -> listof number
;;
;; a version of `sqrt' that takes a list of numbers, and returns a list
;; with twice the elements, holding the two roots of each of the inputs;
;; throws an error if any input is negative.
(define (sqrt+ ns)
    (cond
        [(null? ns)         (error 'sqrt+ "null argument")]
        [(< (car ns) 0)     (error 'sqrt+ "argument < 0")]
        [else   (append 
                    (list (sqrt (car ns)) (- 0 (sqrt (car ns))))
                    (if (empty? (cdr ns))
                        empty
                        (sqrt+ (cdr ns))
                    )
                )
        ])
)

;; bin-op : (number number -> number) (listof number) (listof number) -> (listof number)
;;
;; applies a binary numeric function on all combinations of numbers from
;; the two input lists, and return the list of all of the results
(define (bin-op op ls rs)
    (if (or (null? ls) (null? rs))
        (error 'bin-op "wrong argument: null | empty list")
        (append 
            (map (lambda (q) (op (car ls) q)) rs)
            (if (empty? (cdr ls))
                empty
                (bin-op op (cdr ls) rs)
            )
        )
    )
)

;; evaluates MUWAE expressions by reducing them to numbers
(define (eval expr)
  (type-case MUWAE expr
    [num (n)    n]
    [add (l r)  (bin-op + (eval l) (eval r))]
    [sub (l r)  (bin-op - (eval l) (eval r))]
    [sqrtp (e)  (sqrt+ (eval e))]
    [with (bound-id named-expr bound-body)
          (eval (subst bound-body
                       bound-id
                       (eval named-expr)))]
    [id (name)  (error 'eval "free identifier: ~s" name)]))

;; run : string -> listof number
;;
;; evaluate a MUWAE program contained in a string
(define (run str)
  (eval (parse str)))

;; my tests
;; sqrt
(test (run "{sqrt 9}") '(3 -3))
(test (run "{sqrt 1}") '(1 -1))
(test (run "{sqrt 0}") '(0 0))
(test (run "{sqrt {- 38 2}}") '(6 -6))
(test (run "{sqrt {with {x 49} x}}") '(7 -7))
(test (run "{with {x {sqrt 49}} {+ 1 x}}") '(8 -6))
(test/exn (run "{sqrt {- 1 2}}") "argument < 0")
(test/exn (run "{sqrt -10}") "argument < 0")

;; add, sub
(test (run "{+ {sqrt 1} 3}") '(4 2))
(test (run "{+ {sqrt 4} {sqrt 16}}") '(6 -2 2 -6))
(test (run "{+ {- {+ {sqrt 1} 3} 2} {sqrt 100}}") '(12 -8 10 -10))
(test (run "{sqrt {+ 16 {+ {sqrt {+ 1 -1}} {+ 7 2}}}}") '(5 -5 5 -5))

;; parse
(test/exn (run "{x}") "parse: bad syntax: (x)")

;; eval
(test/exn (run "{sqrt x}") "free identifier: x")

;; testing provided! skeleton
(test/exn (run 1) "ring->sexpr: expects argument of type <string>")
(test/exn (run "'") "syntax error (bad contents)")
(test/exn (run "{+ 1 1} {+ 2 2}") "bad syntax (multiple expressions)")

;; testing internal functions
(test/exn (sqrt+ null) "null argument")
(test/exn (sqrt+ '()) "null argument")
(test/exn (sqrt+ empty) "null argument")

(test/exn (bin-op + null (num (list 1 1))) "wrong argument: null | empty list")
(test/exn (bin-op + (num (list 1 1)) null) "wrong argument: null | empty list")
(test/exn (bin-op + empty (num (list 1 1))) "wrong argument: null | empty list")
(test/exn (bin-op + (num (list 1 1)) empty) "wrong argument: null | empty list")
(test/exn (bin-op + '() (num (list 1 1))) "wrong argument: null | empty list")
(test/exn (bin-op + (num (list 1 1)) '()) "wrong argument: null | empty list")

;; #4
(test (run "{with {x {sqrt 16}} {+ 2 2}}")                  '(4))
(test (run "{with {x {sqrt 16}} {+ 2 x}}")                  '(6 -2))
(test (run "{with {x {sqrt 16}} {+ x x}}")                  '(8 0 0 -8))
(test (run "{with {x {sqrt 16}} {+ {sqrt 16} x}}")          '(8 0 0 -8))
(test (run "{with {x {sqrt 16}} {- x {sqrt 36}}}")          '(-2 10 -10 2))
(test (run "{with {x {+ {sqrt 4} {sqrt 16}}} x}")           '(6 -2 2 -6))
(test (run "{with {x {sqrt 16}} {with {y x} {- x y}}}")     '(0 8 -8 0))
(test (run "{with {x 16}        {with {y x} {- x y}}}")     '(0))
(test (run "{with {x {sqrt 16}} {+ {sqrt 16} {with {y x} {- x y}}}}")
        '(4 12 -4 4 -4 4 -12 -4))
(test (run "{+ {sqrt 4} {with {x {sqrt 16}} {+ x {sqrt 36}}}}")
        '(12 0 4 -8 8 -4 0 -12))
(test (run "{with {x {sqrt 16}} {+ {sqrt 16} {with {y {+ {sqrt 4} x}} {- x y}}}}")
        '(2 10 6 14 -6 2 -2 6 -6 2 -2 6 -14 -6 -10 -2))

;; given tests
;; tests
(test (run "5") '(5))
(test (run "{+ 5 5}") '(10))
(test (run "{with {x {+ 5 5}} {+ x x}}") '(20))
(test (run "{with {x 5} {+ x x}}") '(10))
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") '(14))
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") '(4))
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") '(15))
(test (run "{with {x 5} {+ x {with {x 3} x}}}") '(8))
(test (run "{with {x 5} {+ x {with {y 3} x}}}") '(10))
(test (run "{with {x 5} {with {y x} y}}") '(5))
(test (run "{with {x 5} {with {x x} x}}") '(5))
(test/exn (run "{with {x 1} y}") "free identifier")

;; additional tests for complete coverage
(test (run "{with {x 2} {- {+ x x} x}}") '(2))
(test/exn (run "{with x = 2 {+ x 3}}") "bad syntax")
(test/exn (run "{bleh}") "bad syntax")
