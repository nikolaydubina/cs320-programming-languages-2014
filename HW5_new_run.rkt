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

;; run : string list-of-deffun -> number
(define (run body deffuns)
    (interp-wrapper (parse (string->sexpr body)) deffuns)
)

;; All following tests are PROVIDED NOAH as suppliment to claim. They are given either by TA or professor.

(define env1
  (list
   (parse-defn `{deffun {sum x y} {+ y x}})
   (parse-defn `{deffun {sub x y} {- y x}})
   (parse-defn `{deffun {identity x} x})
   (parse-defn `{deffun {twice x} {+ x x}})
   (parse-defn `{deffun {inc x} {sum 1 x}})
   (parse-defn `{deffun {dec x} {sub 1 x}})
   (parse-defn `{deffun {manyarg a b c d e f g h i j k} c})
   (parse-defn `{deffun {manyarg2 a b c d e f g h i j k} {sum a k}})
   (parse-defn `{deffun {manymanyarg a b c d e f g h i j k} 3})
   (parse-defn `{deffun {noarg} 5})
   (parse-defn `{deffun {withy y} {with {x 10} {sum x y}}})
   (parse-defn `{deffun {withx x} {with {x 10} {sum x x}}})
   (parse-defn `{deffun {f0} 15})
   (parse-defn `{deffun {f1 x} {+ x 10}})
   (parse-defn `{deffun {f2 x y} {- x y}})
   ))


;; tests #2 ~ #101
(test (run "{f0}" env1) 15)
(test (run "{f1 {f0}}" env1) 25)
(test (run "{f2 {f1 {f0}} {f0}}" env1) 10)
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test (run "{sum 1 2}" env1) 3)
(test (run "{sub 3 4}" env1) 1)
(test (run "{identity 5}" env1) 5)
(test (run "{twice 6}" env1) 12)
(test (run "{inc 7}" env1) 8)
(test (run "{manyarg 8 9 10 11 12 13 14 15 16 17 18}" env1) 10)
(test (run "{manyarg2 19 20 21 22 23 24 25 26 27 28 29}" env1) 48)
(test (run "{manymanyarg 30 31 32 33 34 35 36 37 38 39 40}" env1) 3)
(test (run "{manymanyarg 1 2 3 4 5 6 7 8 9 10 11}" env1) 3)
(test (run "{noarg}" env1) 5)
(test (run "{sum {sum 1 2} 3}" env1) 6)
(test (run "{sub {sub 4 5} 6}" env1) 5)
(test (run "{identity {identity 6}}" env1) 6)
(test (run "{twice {twice 7}}" env1) 28)
(test (run "{inc {inc 8}}" env1) 10)
(test (run "{dec {dec 9}}" env1) 7)
(test (run "{sum {sum {sum 1 2} 3} 4}" env1) 10)
(test (run "{sub {sub {sub 5 6} 7} 8}" env1) 2)
(test (run "{identity {identity {identity 9}}}" env1) 9)
(test (run "{twice {twice {twice 10}}}" env1) 80)
(test (run "{inc {inc {inc 11}}}" env1) 14)
(test (run "{dec {dec {dec 12}}}" env1) 9)
(test (run "{identity {sum 4 5}}" env1) 9)
(test (run "{twice {identity {sum 4 5}}}" env1) 18)
(test (run "{identity {twice {sum 4 5}}}" env1) 18)
(test (run "{noarg}" env1) 5)
(test (run "{sum {noarg} {manymanyarg 1 2 3 4 5 6 7 8 9 10 11}}" env1) 8)
(test (run "{manyarg 1 2 {noarg} 4 5 6 7 8 9 10 11}" env1) 5)
(test (run "{manyarg2 {noarg} 2 3 4 5 6 7 8 9 10 {noarg}}" env1) 10)
(test (run "{with {x 1} {withx 7}}" env1) 20)
(test (run "{with {x 1} {withy 7}}" env1) 17)
(test (run "{with {x 1} {with {y 2} {identity {withy x}}}}" env1) 11)
(test (run "{with {x 1} {with {y 2} {withx {withy x}}}}" env1) 20)
(test (run "{with {x 1} {with {y 2} {withy {withx x}}}}" env1) 30)
(test (run "{withy 5}" env1) 15)
(test (run "{withx 5}" env1) 20)
(test (run "{withy {withx {noarg}}}" env1) 30)
(test (run "{withx {withy {noarg}}}" env1) 20)
(test (run "{withy {twice {withy {noarg}}}}" env1) 40)
(test (run "{withx {twice {withx {noarg}}}}" env1) 20)
(test (run "{with {x {f 2 5}} {g x}}" (list (parse-defn '{deffun {f a b} {+ a b}}) (parse-defn '{deffun {g x} {- x 5}}))) 2)
(test (run "{f 1 2}" (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (run "{+ {f} {f}}" (list (parse-defn '{deffun {f} 5}))) 10)
(test (run "{h 1 4 5 6}" (list (parse-defn '{deffun {h x y z w} {+ x w}}) (parse-defn '{deffun {g x y z w} {+ y z}}))) 7)
(test (run "{with {x 10} {- {+ x {f}} {g 4}}}" (list (parse-defn '{deffun {f} 4}) (parse-defn '{deffun {g x} {+ x x}}))) 6)

(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{with {x 3} {with {y 5} {get {rec {a x} {b y}} a}}}" empty) 3)
(test (run "{with {x {f {rec {a 10} {b 5}} 2}} {g x}}" (list (parse-defn '{deffun {f a b} {+ {get a a} b}}) (parse-defn '{deffun {g x} {+ 5 x}}))) 17)
(test (run "{get {f 1 2 3 4 5} c}" (list (parse-defn '{deffun {f a b c d e} {rec {a a} {b b} {c c} {d d} {e e}}}))) 3)
(test (run "{get {f 1 2 3} b}" (list (parse-defn '{deffun {f a b c} {rec {a a} {b b} {c c}}}))) 2)
(test (run "{get {f 1 2 3} y}" (list (parse-defn '{deffun {f a b c} {rec {x a} {y b} {z c} {d 2} {e 3}}}))) 2)
(test (run "{get {f 1 2 3} d}" (list (parse-defn '{deffun {f a b c} {rec {x a} {y b} {z c} {d 2} {e 3}}}))) 2)
(test (run "{f {get {get {rec {a {rec {a 10} {b {- 5 2}}}} {b {get {rec {x 50}} x}}} a} b}}" (list (parse-defn '{deffun {f x} {+ 5 x}}))) 8)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{rec {a 10}}" empty) `record)
(test (run "{get {rec {a 10}} a}" empty) 10)
(test (run "{get {rec {a {+ 1 2}}} a}" empty) 3)
(test (run "{rec }" empty) `record)
(test (run "{get {rec {a {rec {b 10}}}} a}" empty) `record)
(test (run "{get {get {rec {a {rec {a 10}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} b}" empty) 20)
(test (run "{+ {get {rec {a 10}} a} {get {rec {a 20}} a}}" empty) 30)
(test (run "{+ {get {rec {a 10}} a} {get {rec {a 20}} a}}" empty) 30)
(test (run "{rec {a 10}}" empty) `record)
(test (run "{rec {a {- 2 1}}}" empty) `record)
(test (run "{get {rec {a 10}} a}" empty) 10)
(test (run "{get {rec {a {- 2 1}}} a}" empty) 1)
(test (run "{get {rec {a {rec {b 10}}}} a}" empty) `record)
(test (run "{get {get {rec {a {rec {a 10}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} a}" empty) 10)
(test (run "{get {get {rec {a {rec {a 10} {b 20}}}} a} b}" empty) 20)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
(test (run "{with {y {rec {x 1} {y 2} {z 3}}} {get y y}}" empty) 2)
(test (run "{with {y {rec {x 1} {y 2} {z 3}}} {get y z}}" empty) 3)
(test (run "{rec {a 10} {b {+ 1 2}}}" empty) 'record)
(test (run "{get {rec {a 10} {b {+ 1 2}}} b}" empty) 3)
(test (run "{g {rec {a 0} {c 12} {b 7}}}" (list (parse-defn '{deffun {g r} {get r c}}))) 12)
(test (run "{get {rec {r {rec {z 0}}}} r}" empty) 'record)
(test (run "{get {get {rec {r {rec {z 0}}}} r} z}" empty) 0)
