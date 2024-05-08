#lang plai

;; HW5
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

;; uniq?: list-of-symbol -> bool
;;
;; checks whethere all elements in list are unique
(define (uniq? alist)
    (equal? (length (remove-duplicates alist)) (length alist))
)

;; deffun - type whose initializator is function definition
(define-type fundef
    [deffun 
        (fun-name symbol?)
        (arg-name (lambda (q) (and (list? q) (andmap symbol? q) (uniq? q))))
        (body FnWAE?)
    ]
)

;; FnWAE - abstract syntax
(define-type FnWAE
    [num    (n number?)]
    [add    (lhs FnWAE?) (rhs FnWAE?)]
    [sub    (lhs FnWAE?) (rhs FnWAE?)]
    [with   (name symbol?) (named-expr FnWAE?) (body FnWAE?)]
    [id     (name symbol?)]
    [app    (ftn symbol?) (arg (lambda (q) (and (list? q) (andmap FnWAE? q))))]
    [rec    (arg (lambda (q)
                (and 
                    (list? q)
                    (andmap (lambda (t) (and (pair? t) (symbol? (first t)) (or (FnWAE? (second t))))) q)
                )
            ))]
    [get    (body FnWAE?) (va symbol?)]
)

;; safesymbol: symbol -> symbol
;;
;; if symbol is qual to 'numV, then error is thrown at 'parse function
;; otherwise symbol is returned
(define (safesymbol x)
    (if (equal? x 'numV)
        (error 'parse "numV is reserved. use another, there're plenty other")
        x)
)

;; parse : sexp -> FnWAE
(define (parse sexp)
    (match sexp
        [(? number?)                (num sexp)]
        [(list '+ l r)              (add (parse l) (parse r))]
        [(list '- l r)              (sub (parse l) (parse r))]
        [(list 'with (list x i) b)  (with (safesymbol x) (parse i) (parse b))]
        [(? symbol?)                (id (safesymbol sexp))]
        [(list 'get body va)        (get (parse body) va)]
        [(list f-rec a ...)
            (match f-rec
                ['rec (rec ((lambda (q)
                                (if (uniq? (map car q))
                                    q
                                    (error 'parse "duplicate fields")
                                ) 
                            ) (map (lambda (q) (list (safesymbol (first q)) (parse (second q)))) a))
                        )]
                ['numV              (safesymbol 'numV)]
                [(? symbol?)        (app f-rec (map parse a))]
                [else (error 'parse "unexpected construction")]
            )]
    )
)

;; parse-defn : sexp -> deffun
(define (parse-defn sexp)
    (match sexp
        [(list 'deffun (list f x ...) body)
            (unless (uniq? x) (error 'parse-defn "bad syntax"))
            (deffun (safesymbol f) x (parse body))
        ]
    )
)

;; lookup-deffun : symbol list-of-deffun -> deffun
(define (lookup-deffun name deffuns)
    (cond
        [(empty? deffuns)   (error 'lookup-deffun "unknown function")]
        [else
            (if (symbol=? name (deffun-fun-name (first deffuns)))
                (first deffuns)
                (lookup-deffun name (rest deffuns))
            )
        ]
    )
)

;; subst-list: FnWAE list-of-symbol list-of-number -> FnWAE
;;
;; substitutes each occurence of each element in list-of-symbol in FnWAE to correspondent
;; element in list-of-number
;; NOTE: lengths of input lists should equal
(define (subst-list fnwae vars args)
    (if (or (empty? vars) (empty? args))
        fnwae
        (subst-list (subst fnwae (car vars) (car args)) (cdr vars) (cdr args))
    )
)

;; Additional functions for substitution and interpretation
;; =========================================================
;;
;; in interpretation FnWAE is translated into a list with following specifications:
;;  <number> -> (list (list 'numV <number>))
;;  <record> -> (list (list <symbol> 
;;                                  | <record>
;;                                  | <number>))
;; NOTE: record === raw list of either (lists of symbol and record) or ('numV and number)

;; fromrec: record -> num
;;                      | record
;;
;; returns a number or list itself accordingly
;;
;; used in substitution and interpretation
(define (fromrec record)
    (if (equal? (first (first record)) 'numV)
        (second (first record))
        record
    )
)

;; fromrectonumber: record -> number
;;
;; returns a number
;;
;; used in substitution
(define (fromrectonumber record)
    (if (and (equal? (first (first record)) 'numV) (number? (second (first record))))
        (second (first record))
        (error 'fromrectonumber "number is required, record passed")
    )
)

;; torec: number -> record
;;
;; translates number into record
;;
;; used in substitution and interpretation
(define (torec n)
    (if (number? n)
      (list (list 'numV n))
      (error 'torec "number is required, record passed")
    )
)

;; fromtorec: record -> rec
;;
;; translates record into FnWAE type with either
;; -> rec constructor
;; -> num constructor
;;
;; used in substitution
(define (fromtorec record)
    (rec (map (lambda (q) (list (first q)
        (if (number? (fromrec (second q)))
            (num (fromrec (second q)))
            (fromtorec (second q))
        ))) record))
)

;; subst : FnWAE symbol record -> FnWAE
(define (subst fnwae x val)
    (type-case FnWAE fnwae
        [num (n)    (num n)]
        [add (l r)  (add (subst l x val) (subst r x val))]
        [sub (l r)  (sub (subst l x val) (subst r x val))]
        [with (y i b) 
            (with y (subst i x val)
                (if (symbol=? y x)
                    b
                    (subst b x val)
                )
            )
        ]
        [id (s)     (if (symbol=? s x)
                        (if (number? (fromrec val))
                            (num (fromrec val))
                            (fromtorec val)
                        )
                        fnwae )]
        [app (f a)  (app f (map (lambda (q) (subst q x val)) a))]
        [rec (a)    (rec (map (lambda (q) (list (first q) (subst (second q) x val))) a))]
        [get (a b)  (get (subst a x val) b)]
    )
)

;; interp : FnWAE list-of-deffun -> record
;;
;; if record is in form of (list (list 'numV <number>)) it is considered as "number" and treated accordingly
;; otherwise, it is treated as a record
;; the same applies for a return value
(define (interp fnwae deffuns)
    (type-case FnWAE fnwae
        [num (n)    (torec n)]
        [add (l r)  (torec (+ (fromrectonumber (interp l deffuns)) (fromrectonumber (interp r deffuns))))]
        [sub (l r)  (torec (- (fromrectonumber (interp l deffuns)) (fromrectonumber (interp r deffuns))))]
        [with (n e b) (interp (subst b n (interp e deffuns)) deffuns)]
        [id (s) (error 'interp "free variable")]
        [app (f a)  (local [
                           (define a-deffun (lookup-deffun f deffuns))
                           (define a-vars   (deffun-arg-name (lookup-deffun f deffuns)))
                           (define a-args   (map (lambda (q) (interp q deffuns)) a))
                           ]
                (if (eq? (length a-vars) (length a-args))
                    (interp (subst-list (deffun-body a-deffun) a-vars a-args) deffuns)
                    (error 'interp "wrong arity")
                )
            )]
        [rec (a) (map 
                (lambda (q)
                    (list (first q) (interp (second q) deffuns))
                ) a )]
        [get (body va)
                ((lambda (q)
                        (if (empty? q)
                            (error 'interp "no such field")
                            (second (first q))
                        )
                    ) (filter (lambda (q) (equal? (first q) va)) (interp body deffuns))
                )
            ]
    )
)

;; intrep-wrapper: sexpr list-of-deffun -> 
;;                      | 'parse 
;;                      | number
;;
;; if FnWAE is record, then it returns 'parse
;; otherwise, number
(define (interp-wrapper sexpr deffuns)
    ((lambda (q) (if (equal? (first (first q)) 'numV) (fromrec q) 'record)) (interp sexpr deffuns))
)

;; run : string string -> number
(define (run body deffuncs)
    (if (equal? deffuncs "{}")
        (interp-wrapper (parse (string->sexpr body)) empty )
        (interp-wrapper (parse (string->sexpr body)) (list (parse-defn (string->sexpr deffuncs))))
    )
)

;; tests
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}"  "{}") 0)
(test (run "{get {rec {a 1}} a}"                    "{}") 1)
(test (run "{get {rec {a 1} {b 2} {c 3}} a}"        "{}") 1)
(test (run "{rec {a 10} {b {+ 1 2}}}"               "{}") 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}"       "{}") 3)
(test (run "{get {rec {r {rec {z 0}}}} r}"          "{}") 'record)
(test (run "{g {rec {a 0}}}"                        "{deffun {g r} {get r a}}") 0)
(test (run "{g {rec {a 0} {c 12} {b 7}}}"           "{deffun {g r} {get r c}}") 12)

(test (run "{f 1 2}"        "{ deffun { f x y } { + x y }}") 3)
(test (run "{+ {f} {f} }"   "{ deffun { f } 5 }") 10)

(test (run "{f}"            "{ deffun { f } 5 }") 5)
(test (run "{+ 1 2}"        "{ deffun { f } 5}") 3)
(test (run "{ f 2 2 3}"     "{ deffun { f a b c} { + a {+ b c}}}") 7)
(test (run "{ f 1 {f 1 3}}" "{ deffun { f a b} {- b a}}") 1)

(test/exn (run "{ f 1 {f x 3}}" "{ deffun { f a b} {- b a}}") "free variable")
(test/exn (run "{ f 1 2 3}"     "{ deffun { f } 5}")    "interp: wrong arity")
(test/exn (run "{ x 1 2}"       "{ deffun { f x x} 5}") "parse-defn: bad syntax")
(test/exn (run "{ x 1 2}"       "{ deffun { y } 5}")    "lookup-deffun: unknown function")
(test/exn (run "{f 1}"      "{ deffun { f x y } { + x y }}") "interp: wrong arity")
(test/exn (run "{rec {z {get {rec {z 0}} y}}}"      "{}") "interp: no such field")
(test/exn (run "{get {rec {b 10} {b {+ 1 2}}} b}"   "{}") "parse: duplicate fields")
(test/exn (run "{get {rec {a 10}} b}"               "{}") "no such field")
(test/exn (run "{+ 1 {rec {a 10}}}"                 "{}") "fromrectonumber: number is required, record passed")
(test/exn (run "{with {numV 5} numV}"               "{}")             "parse: numV is reserved. use another, there're plenty other")
(test/exn (run "{with {numV 5} 3}"                  "{}")             "parse: numV is reserved. use another, there're plenty other")
(test/exn (run "{rec {numV 10}}" "{}")                                "parse: numV is reserved. use another, there're plenty other")
(test/exn (run "{numV 1}"                  "{deffun {f x} {+ x 1}}")  "parse: numV is reserved. use another, there're plenty other")
(test/exn (run "{f 1}"                  "{deffun {numV x} {+ x 1}}")  "parse: numV is reserved. use another, there're plenty other")
(test/exn (run "{1 1}" "{}")    "parse: unexpected construction")

;; add.tests.0
(test/exn (run 1 "{}") "ring->sexpr: expects argument of type <string>")
(test/exn (run "'" "{}") "syntax error (bad contents)")
(test/exn (run "{+ 1 1} {+ 2 2}" "{}") "bad syntax (multiple expressions)")

;; add.tests.1
(test (run "{with {x 5} {+ x x}}" "{}") 10)
(test (run "{with {x {with {a 1} {+ a 4}}} {+ x x}}" "{}") 10)
(test (run "{with {x 5} {+ x {with {x 3} x}}}" "{}") 8)
(test (run "{with {y 5} {+ 3 {with {x 3} y}}}" "{}") 8)
(test (run "{with {y 5} { f y }}" "{ deffun {f x } x}") 5)
(test (run "{with {x 4} {rec {a x}}}"  "{}") 'record)
(test (run "{with {x 4} {get {rec {a x}} a}}"  "{}") 4)

;; add.tests.2
(define b (fromtorec (list (list 'a (list (list 'b (list (list 'numV 2))))))))
(test b (parse (string->sexpr "{rec {a {rec {b 2}}}}")))

(test (run "{with {x {rec {a 0}}} {get x a}}" "{}") 0)
(define a (fromtorec (list (list 'a (list (list 'numV 2))))))
(test a (parse (string->sexpr "{rec {a 2}}")))

(test/exn (torec (parse (string->sexpr "{rec {a 10}}"))) "torec: number is required, record passed")
(test (safesymbol 'a) 'a)
(test/exn (safesymbol 'numV) "parse: numV is reserved. use another, there're plenty other")
