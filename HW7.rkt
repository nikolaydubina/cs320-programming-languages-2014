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

(define-type KCFAE
  [num (n number?)]
  [add (lhs KCFAE?)
       (rhs KCFAE?)]
  [sub (lhs KCFAE?)
       (rhs KCFAE?)]
  [id (name symbol?)]
  [fun (args (lambda (q) (and (list? q) (andmap symbol? q))))
       (body KCFAE?)]
  [app (fun-expr KCFAE?)
       (arg-expr (lambda (q) (and (list? q) (andmap KCFAE? q))))]
  [if0 (test KCFAE?)
       (then KCFAE?)
       (else KCFAE?)]
  [withcc (name symbol?)
          (body KCFAE?)]
  [try-catch (body KCFAE?)
             (catch KCFAE?)]
  [throw (self null?)]
)

(define-type KCFAE-Value
  [numV (n number?)]
  [closureV (param (lambda (q) (and (list? q) (andmap symbol? q))))
            (body KCFAE?)
            (sc DefrdSub?)]
  [contV (proc procedure?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value KCFAE-Value?)
        (rest DefrdSub?)])

;; ----------------------------------------

;; parse-sexpr : S-expr -> KCFAE
(define (parse-sexpr sexp)
    (cond
        [(number? sexp) (num sexp)]
        [(symbol? sexp) (id sexp)]
        [(pair? sexp)
            (case (car sexp)
                [(throw) (throw null)]
                [(+) (add (parse-sexpr (second sexp)) (parse-sexpr (third sexp)))]
                [(-) (sub (parse-sexpr (second sexp)) (parse-sexpr (third sexp)))]
                [(fun) (fun (second sexp) (parse-sexpr (third sexp)))]
                [(if0) (if0 (parse-sexpr (second sexp))
                            (parse-sexpr (third sexp))
                            (parse-sexpr (fourth sexp)))]
                [(withcc) (withcc (second sexp) (parse-sexpr (third sexp)))]
                [(try) (try-catch (parse-sexpr (second sexp)) (parse-sexpr (fourth sexp)))]
                [else (app (parse-sexpr (first sexp)) (map parse-sexpr (cdr sexp)))]
            )
        ]
    )
)

;; parse: string -> KCFAE
;; parses a string containing a KCFAE expression to a KCFAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

(test (parse "3") (num 3))
(test (parse "x") (id 'x))
(test (parse "{+ 1 2}") (add (num 1) (num 2)))
(test (parse "{- 1 2}") (sub (num 1) (num 2)))
(test (parse "{if0 0 1 2}") (if0 (num 0) (num 1) (num 2)))
(test (parse "{withcc x 2}") (withcc 'x (num 2)))

;; my tests
;; #1
(test (parse "{fun {x} x}") (fun (list 'x) (id 'x)))
(test (parse "{fun {x y} x}") (fun (list 'x 'y) (id 'x)))
(test (parse "{1 2}") (app (num 1) (list (num 2))))
(test (parse "{1 2 x}") (app (num 1) (list (num 2) (id 'x))))
(test (parse "{x}") (app (id 'x) '()))
;; #2
(test (parse "{throw}") (throw null))
(test (parse "{+ 1 {throw}}") (add (num 1) (throw null)))
(test (parse "{try 7 catch 8}") (try-catch (num 7) (num 8)))

;; ----------------------------------------

;; interp-args: (list of KCFAE) (list of KCFA-Value) DefrdSub (list of KCFAE) (KCFAE-Value -> alpha) -> alpha
(define (interp-args arg-expr arg-vals ds c k)
    (if (not (empty? arg-expr))
        (interp (car arg-expr) ds c
            (lambda (q)
                (interp-args (cdr arg-expr) (append arg-vals (list q)) ds c k)
            )
        )
        (k arg-vals)
    )
)

;; pushn-sub: (list of symbols) (list of KCFAE-Value) ds -> ds
(define (pushn-sub params args ds)
    (if (and (or (empty? params) (empty? args)) (or (not (empty? params)) (not (empty? args))))
        (error 'pushn-sub "N of params != N of args")
        (if (empty? params)
            ds
            (aSub (car params) (car args) (pushn-sub (cdr params) (cdr args) ds))
        )
    )
)

;; interp : KCFAE DefrdSub (list of (pair KCFAE DefrdSub (KCFAE-Value -> alpha))) (KCFAE-Value -> alpha) -> alpha
(define (interp a-fae ds c k)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds c
                       (lambda (v1)
                         (interp r ds c
                                 (lambda (v2)
                                   (k (num+ v1 v2))))))]
    [sub (l r) (interp l ds c
                       (lambda (v1)
                         (interp r ds c
                                 (lambda (v2)
                                   (k (num- v1 v2))))))]
    [id (name) (k (lookup name ds))]
    [fun (param body-expr)
         (k (closureV param body-expr ds))]
    [app (fun-expr arg-expr)
        (interp fun-expr ds c
            (lambda (fun-val)
                (interp-args arg-expr '() ds c
                    (lambda (arg-vals)
                        (type-case KCFAE-Value fun-val
                            [closureV (params body ds)
                                      (interp body (pushn-sub params arg-vals ds) c k)]
                            [contV (k)
                                   (k (car arg-vals))]
                            [else (error 'interp "not a function")]
                        )
                    )
                )
            )
        )
    ]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds c
                 (lambda (v)
                   (if (numzero? v)
                       (interp then-expr ds c k)
                       (interp else-expr ds c k))))]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id (contV k) ds)
                    c k)]
    [try-catch (body catch)
               (interp body ds (append (list (list catch ds k)) c) k)]
    [throw (self) (interp (first (car c)) (second (car c)) (cdr c) (third (car c)))]
  )
)

;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op +))
(define num- (num-op -))

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-sc)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-sc))]))

(test/exn (lookup 'x (mtSub)) "free variable")
(test (lookup 'x (aSub 'x (numV 9) (mtSub))) (numV 9))
(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 9) (mtSub)))) (numV 9))

;; interp-expr : KCFAE -> number-or-'function
(define (interp-expr a-fae)
  (type-case KCFAE-Value (interp a-fae (mtSub) '() (lambda (x) x))
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]))

; run : string -> number-or-'function
;; evaluate a KCFAE program contained in a string
(define (run str)
  (interp-expr (parse str)))

(test (run "10") 10)
(test (run "{fun {x} x}") 'function)
(test (run "{withcc x x}") 'function)
(test (run "{+ 10 7}") 17)
(test (run "{- 10 7}") 3)
(test (run "{{fun {x} {+ x 12}} {+ 1 17}}") 30)
(test (run "{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}} {fun {y} {+ x y}}}} 0}") 3)
(test (run "{withcc k {k 10}}") 10)
(test (run "{withcc k {+ {k 10} 17}}") 10)
;; Check for eager evaluation:
(test/exn (run "{{fun {x} 0} {1 {fun {y} y}}}") "not a function")

;; #1
;; given tests
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)

;; my tests
(test (run "{{fun {x y z} {{fun {} {+ x {+ y z }}}}} 1 2 3}") 6)
(test (run "{{{fun {} {fun {} 10}}}}") 10)

;; additional tests
(test/exn (run "{{fun {x y} 10} 1}") "N of params != N of args")
(test/exn (run "{{fun {} 10} 1}") "N of params != N of args")
(test/exn (run "{{fun {a b c} 10} }") "N of params != N of args")

;; #2
;; given tests
(test (run "{try 7 catch 8}") 7)
(test (run "{try {throw} catch 8}") 8)
(test (run "{try {+ 1 {throw}} catch 8}") 8)
(test (run "{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}") 8)
(test (run "{try {try {throw} catch 8} catch 9}") 8)
(test (run "{try {try {throw} catch {throw}} catch 9}") 9)
(test (run "{try {try 7 catch {throw}} catch 9}") 7)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
;; my tests
(test (run "{try {try {throw} catch {try 10 catch {throw}}} catch 9}") 10)
(test (run "{try {try {throw} catch {try {throw} catch {throw}}} catch 9}") 9)
(test (run "{try {try {throw} catch {try {throw} catch {+ 6 2}}} catch 9}") 8)
(test (run "{{fun {x} {try {throw} catch x}} 42}") 42)
(test (run "{{fun {x} {try x catch 10} } 42}") 42)
(test (run "{{fun {x} {try {{fun {x} {+ {throw} x}} 10} catch x} } 42}") 42)

;; #2 && #1
(test (run "{{fun {x} {+ 1 x }} {try {throw} catch 10}}") 11)
(test (run "{{fun {x} {try 5 catch x}} {try {throw} catch 10}}") 5)


;; LeVn tests

(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{{fun {x y} {- y x}} {+ 8 2} {- 16 4}}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
;;old tests
(test (run "10")
        10)
  (test (run "{fun {x} x}")
        'function)
  (test (run "{withcc x x}")
        'function)
  (test (run "{+ 10 7}")
        17)
  (test (run "{- 10 7}")
        3)
  (test (run "{{fun {x} {- x 12}} {+ 1 17}}")
        6)
  (test (run "{{fun {x} {{fun {f} {+ {f 1} {{fun {x} {f 2}} 3}}}
                         {fun {y} {+ x y}}}}
               0}")
        3)
  (test (run "{withcc k {k 10}}")
        10)
  (test (run "{withcc k {+ {k 10} 17}}")
        10)
 
(test (run "{try 7 catch 8}")
        7)

 (test (interp-expr (try-catch (num 7) (num 8)))
        7)
 ;;
  (test (run "{try {throw} catch 8}")
        8)
  
  (test (interp-expr (try-catch (throw null) (num 8))) 
        8)
  
  
  (test (run "{try {+ 1 {throw}} catch 8}")
        8)
  (test (run "{{fun {f} {try {f 3} catch 8}}
               {fun {x} {throw}}}")
        8)
  (test (run "{try {try {throw} catch 8} catch 9}")
        8)
  (test (run "{try {try {throw} catch {throw}} catch 9}")
        9)
  (test (run "{try {try 7 catch {throw}} catch 9}")
        7)
  (test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}}
               {fun {x} {throw}}}")
	8)
  
  (test (interp-expr
         (app
          (fun
           (list 'mk-list)
           (app
            (fun
             (list 'list)
             (if0
              (app (id 'list) (list (num 0)))
              (app (id 'list) (list (num 1)))
              (app
               (num 0)
               (list (app
                      (app (id 'list) (list (num 2)))
                      (list (app
                             (app
                              (app (id 'mk-list) (list (sub (app (id 'list) (list (num 0))) (num 1))))
                              (list (add (app (id 'list) (list (num 1))) (num 2))))
                             (list (app (id 'list) (list (num 2)))))))))))
            (list (withcc 'k (app (app (app (id 'mk-list) (list (num 3))) (list (num 0))) (list (id 'k)))))))
          (list (fun
                 (list 'a)
                 (fun (list 'b) (fun (list 'c) (fun (list 'sel) 
                                                    (if0 (id 'sel) 
                                                         (id 'a) 
                                                         (if0 (sub (id 'sel) (num 1)) (id 'b) (id 'c))))))))))
        6)
