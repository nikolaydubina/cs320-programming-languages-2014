#lang plai

;;(print-only-errors #t)

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

(define-type WFAE
    [num (n number?)]
    [id  (name symbol?)]
    [add (lhs WFAE?) (rhs WFAE?)]
    [sub (lhs WFAE?) (rhs WFAE?)]
    [fun (arg symbol?) (body WFAE?)]
    [app (fun-expr WFAE?) (arg-expr WFAE?)]
    [with (name id?) (named-expr WFAE?) (body WFAE?)]
)

(define-type CWFAE
    [cnum (n number?)]
    [cid  (pos number?)]
    [cadd (lhs CWFAE?) (rhs CWFAE?)]
    [csub (lhs CWFAE?) (rhs CWFAE?)]
    [cfun (body CWFAE?)]
    [capp (fun-expr CWFAE?) (arg-expr CWFAE?)]
    [cwith (named-expr CWFAE?) (body CWFAE?)]
)

(define-type CWFAE-Value
    [numV (n number?)]
    [closureV (body CWFAE?) (ds DefrdSub?)]
)

(define-type CDefrdSub
    [mtCSub]
    [aCSub (value symbol?) (rest CDefrdSub?)]
)

(define-type CWFAE-Cont
    [mtK]
    [addSecond (rhs CWFAE?) (ds DefrdSub?) (k CWFAE-Cont?)]
    [doAdd (v CWFAE-Value?) (k CWFAE-Cont?)]
    [subSecond (rhs CWFAE?) (ds DefrdSub?) (k CWFAE-Cont?)]
    [doSub (v CWFAE-Value?) (k CWFAE-Cont?)]
    [appArg (arg-expr CWFAE?) (ds DefrdSub?) (k CWFAE-Cont?)]
    [doApp (v CWFAE-Value?) (k CWFAE-Cont?)]
    [doWith (v CWFAE?) (ds DefrdSub?) (k CWFAE-Cont?)]
)

(define (DefrdSub? x) true)

;; parse-sexpr : S-expr -> WFAE
(define (parse-sexpr sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse-sexpr (second sexp))
                 (parse-sexpr (third sexp)))]
       [(-) (sub (parse-sexpr (second sexp))
                 (parse-sexpr (third sexp)))]
       [(with) (with (parse-sexpr (first (second sexp)))
                     (parse-sexpr (second (second sexp)))
                     (parse-sexpr (third sexp)))]
       [(fun) (fun (first (second sexp)) (parse-sexpr (third sexp)))]
       [else (app (parse-sexpr (first sexp))
                  (parse-sexpr (second sexp)))])]))

;; parse: string -> WFAE
;; parses a string containing a WFAE expression to a WFAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; compile : WFAE CDefrdSub -> CWFAE
(define (compile wfae ds)
    (type-case WFAE wfae
        [num (n) (cnum n)]
        [id  (name) (cid (locate name ds))]
        [add (lhs rhs) (cadd (compile lhs ds) (compile rhs ds))]
        [sub (lhs rhs) (csub (compile lhs ds) (compile rhs ds))]
        [fun (arg body) (cfun (compile body (aCSub arg ds)))]
        [app (fun-expr arg-expr) (capp (compile fun-expr ds) (compile arg-expr ds))]
        [with (name named-expr body) (cwith (compile named-expr ds) (compile body (aCSub (id-name name) ds)))]
    )
)

;; locate : symbol CDefrdSub -> number
(define (locate name ds)
    (type-case CDefrdSub ds
        [mtCSub () (error 'locate "identifier is not specified")]
        [aCSub (value rest)
            (if (eq? name value)
                0
                (+ 1 (locate name rest))
            )]
    )
)

(define cwfae-reg (cnum 0))
(define k-reg (mtK))
(define v-reg (numV 0))
(define ds-reg empty)

;; interp : -> CWFAE-Value
(define (interp)
    (type-case CWFAE cwfae-reg
        [cnum (n)
            (begin
                (set! v-reg (numV n))
                (continue))]
        [cid (pos)
            (begin
                (set! v-reg (list-ref ds-reg pos))
                (continue))]
        [cadd (lhs rhs)
            (begin
                (set! cwfae-reg lhs)
                (set! k-reg (addSecond rhs ds-reg k-reg))
                (interp))]
        [csub (lhs rhs)
            (begin
                (set! cwfae-reg lhs)
                (set! k-reg (subSecond rhs ds-reg k-reg))
                (interp))]
        [cfun (body)
            (begin
                (set! v-reg (closureV body ds-reg))
                (continue))]
        [capp (fun-expr arg-expr)
            (begin
                (set! cwfae-reg fun-expr)
                (set! k-reg (appArg arg-expr ds-reg k-reg))
                (interp))]
        [cwith (named-expr body)
            (begin
                (set! cwfae-reg named-expr)
                (set! k-reg (doWith body ds-reg k-reg))
                (interp))]
    )
)

;; continue : -> CWFAE-Value
(define (continue)
    (type-case CWFAE-Cont k-reg
        [mtK () v-reg]
        [addSecond (rhs ds k)
            (begin
                (set! cwfae-reg rhs)
                (set! ds-reg ds)
                (set! k-reg (doAdd v-reg k))
                (interp))]
        [doAdd (v k)
            (begin
                (set! v-reg (numV (+ (numV-n v) (numV-n v-reg))))
                (set! k-reg k)
                (continue))]
        [subSecond (rhs ds k)
            (begin
                (set! cwfae-reg rhs)
                (set! ds-reg ds)
                (set! k-reg (doSub v-reg k))
                (interp))]
        [doSub (v k)
            (begin
                (set! v-reg (numV (- (numV-n v) (numV-n v-reg))))
                (set! k-reg k)
                (continue))]
        [appArg (arg-expr ds k)
            (begin
                (set! k-reg (doApp v-reg k))
                (set! ds-reg ds)
                (set! cwfae-reg arg-expr)
                (interp))]
        [doApp (v k)
            (begin
                (set! cwfae-reg (closureV-body v))
                (set! ds-reg (cons v-reg (closureV-ds v)))
                (set! k-reg k)
                (interp))]
        [doWith (body ds k)
            (begin
                (set! cwfae-reg body)
                (set! ds-reg (cons v-reg ds))
                (set! k-reg k)
                (interp))]
    )
)

;; init : void -> void
(define (init)
  (set! k-reg (mtK))
  (set! v-reg (numV 0))
  (set! ds-reg empty))

;; run : string -> CWFAE-Value
;; evaluate a WFAE program contained in a string
(define (run str)
  (begin
    (set! cwfae-reg (compile (parse str) (mtCSub)))
    (init)
    (interp)))

(test (run "10") (numV 10))
(test (run "{+ 10 7}") (numV 17))
(test (run "{- 10 7}") (numV 3))
(test (run "{{fun {x} {+ x 12}} {+ 1 17}}") (numV 30))
(test (run "{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}}
                       {fun {y} {+ x y}}}} 0}") (numV 3))

;; my
(test (run "{with {x 5} {+ x {with {x 3} x}}}") (numV 8))
(test (run "{with {y 5} {+ 3 {with {x 3} y}}}") (numV 8))
(test (run "{with {x {+ 5 5}} {+ x x}}") (numV 20))
(test (run "{with {x 5} {+ x x}}") (numV 10))
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") (numV 14))
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") (numV 4))
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") (numV 15))
(test (run "{with {x 5} {+ x {with {x 3} x}}}") (numV 8))
(test (run "{with {x 5} {+ x {with {y 3} x}}}") (numV 10))
(test (run "{with {x 5} {with {y x} y}}") (numV 5))
(test (run "{with {x 5} {with {x x} x}}") (numV 5))

(test (run "{{fun {x} {+ {with {x 32} x} 10}} 42}") (numV 42))

;; additional tests
(test/exn (run "{with {x 5} {with {x y} x}}") "identifier is not specified")

;; testing provided! skeleton
(test/exn (string->sexpr 1) "ring->sexpr: expects argument of type <string>")
(test/exn (string->sexpr "'") "syntax error (bad contents)")
(test/exn (string->sexpr "{+ 1 1} {+ 2 2}") "bad syntax (multiple expressions)")


;; Le Vn tests
(test (run "{with {x 5} {+ x x}}") (numV 10))
(test (run "{with {x {with {a 1} {+ a 4}}} {+ x x}}" ) (numV 10))
(test (run "{with {x 5} {+ x {with {x 3} x}}}") (numV 8))
(test (run "{with {y 5} {+ 3 {with {x 3} y}}}") (numV 8))
(test (run "5" ) (numV 5))
(test (run "{+ 5 5}" ) (numV 10))
(test (run "{with {x {+ 5 5}} {+ x x}}" ) (numV 20))
(test (run "{with {x 5} {+ x x}}" ) (numV 10))
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}" ) (numV 14))
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}" ) (numV 4))
(test (run "{with {x 5} {+ x {with {x 3} 10}}}" ) (numV 15))
(test (run "{with {x 5} {+ x {with {x 3} x}}}" ) (numV 8))
(test (run "{with {x 5} {+ x {with {y 3} x}}}" ) (numV 10))
(test (run "{with {x 5} {with {y x} y}}" ) (numV 5))
(test (run "{with {x 5} {with {x x} x}}" ) (numV 5))
(test (run "{{fun {x} {- x 12}} {+ 1 17}}") (numV 6))
(test (run "10") (numV 10))
(test (run "{+ 10 7}") (numV 17))
(test (run "{- 10 7}") (numV 3))
(test (run "{{fun {x} {+ x 12}} {+ 1 17}}") (numV 30))
(test (run "{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}} {fun {y} {+ x y}}}} 0}") (numV 3))

;; Dauren's tests
(test (run "{with {x {fun {x} {+ x x}}} {x 10}}") (numV 20))
(test (run "{{fun {f} {f 10}} {fun {f} {+ f {- 10 3}}}}") (numV 17))
(test (run "{with {y {fun {y} {y 5}}} {{fun {t} {t y}} {fun {y} {y {fun {x} {+ 5 x}}}}}}") (numV 10))
(test (run "{with {x 10} {with {y {fun {x} {+ 20 x}}} {with {z {y {+ 30 {{fun {z} {+ z x}} 0} }}} {+ 10 z} } } }") (numV 70))
(test (run "{with {x {fun {x} x}} {x 5}}") (numV 5))
(test (run "{with {x {fun {x} x}} x}") (closureV (cid 0) '()))