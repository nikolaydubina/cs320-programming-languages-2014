#lang plai-typed

;; additional function to check whether type of an argument is boolean
;; any -> boolean
(define (isbool val)
  (or (equal? val false) (equal? val true) (equal? val #f) (equal? val #t))
)

(define-type TMFAE
  [bool (val : boolean)]
  [num (n : number)]
  [pair (fst : TMFAE)
        (snd : TMFAE)]
  [fst (val : TMFAE)]
  [snd (val : TMFAE)]
  [add (lhs : TMFAE)
       (rhs : TMFAE)]
  [sub (lhs : TMFAE)
       (rhs : TMFAE)]
  [id (name : symbol)]
  [eq (lhs : TMFAE)
      (rhs : TMFAE)]
  [ifthenelse (cnd : TMFAE)
      (exprt : TMFAE)
      (exprf : TMFAE)]
  [fun (params : (listof symbol))
       (paramtys : (listof TE))
       (body : TMFAE)]
  [app (fun-expr : TMFAE)
       (arg-exprs : (listof TMFAE))]
  [with (names : (listof symbol))
        (nametys : (listof TE))
        (inits : (listof TMFAE))
        (body : TMFAE)]
  [try1 (try-expr : TMFAE)
        (catch-exprs : TMFAE)]
  [throw]
  )

(define-type TE
  [numTE]
  [boolTE]
  [crossTE (fst : TE)
           (snd : TE)]
  [arrowTE (args : (listof TE))
           (result : TE)]
)

(define-type TMFAE-Value
  [numV (n : number)]
  [boolV (val : boolean)]
  [crossV (fst : TMFAE-Value)
          (snd : TMFAE-Value)]
  [closureV (params : (listof symbol))
            (body : TMFAE)
            (ds : DefrdSub)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol)
        (value : TMFAE-Value)
        (rest : DefrdSub)])

(define-type Type
  [numT]
  [boolT]
  [crossT (fst : Type)
          (snd : Type)]
  [arrowT (param : (listof Type))
          (result : Type)]
  [anyT]
)

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

;; ----------------------------------------

;; evaluetes two TMFAE iteratively and passes them to callback
(define (gettwo a b ds c clbk)
    (interp a ds (lambda (q1) 
        (interp b ds (lambda (q2)
            (clbk q1 q2))
        c))
    c)
)

;; listof symbols listof TMFAE DefrdSub error callback
(define (getn params args ods nds c clbk)
    (if (empty? params)
        (clbk nds)
        (interp (first args) ods (lambda (q)
            (getn (rest params) (rest args) ods (aSub (first params) q nds) c clbk)
        ) c)
    )
)

;; interp : TMFAE DefrdSub -> TMFAE-Value
(define (interp tmfae ds k c)
  (type-case TMFAE tmfae
    [bool (val) (if (isbool val) 
                  (k (boolV val))
                  (error 'iterp "required bool"))]
    [num (n) (k (numV n))]
    [pair (fst snd) 
        (gettwo fst snd ds c (lambda (a b) (k (crossV a b))))]
    [fst (val) (interp val ds (lambda (a) (k (crossV-fst a))) c)]
    [snd (val) (interp val ds (lambda (a) (k (crossV-snd a))) c)]
    [add (l r) (gettwo l r ds c (lambda (a b) (k (num+ a b))))]
    [sub (l r) (gettwo l r ds c (lambda (a b) (k (num- a b))))]
    [id (name) (k (lookup name ds))]
    [eq (l r) (gettwo l r ds c (lambda (l r)
            (if (equal? l r)
                (k (boolV true))
                (k (boolV false))
            )))]
    [ifthenelse (cnd exprt exprf)
        (interp cnd ds (lambda (q)
            (gettwo exprt exprf ds c (lambda (a b)
                (if (boolV-val q)
                    (k a)
                    (k b)))))
        c)]
    [fun (params paramtys body-expr)
         (k (closureV params body-expr ds))]
    [app (fun-expr arg-expr)
        (interp fun-expr ds (lambda (f)
            (getn (closureV-params f) arg-expr ds (closureV-ds f) c (lambda (newds)
                (interp (closureV-body f) newds k c)
            )))
        c)]
    [with (names nametys inits body)
        (getn names inits ds ds c (lambda (newds)
            (interp body newds k c)
        )
    )]
    [try1 (try-expr catch-exprs)
          (interp try-expr ds k (lambda () (interp catch-exprs ds k c)))]
    [throw () (c)]
  )
)

;; num-op : (number number -> number) -> (TMFAE-Value TMFAE-Value -> TMFAE-Value)
(define (num-op op x y)
  (numV (op (numV-n x) (numV-n y))))

(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-ds)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-ds))]))

;; ----------------------------------------

(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]))

;; ----------------------------------------

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [crossTE (fst snd) (crossT (parse-type fst) 
                               (parse-type snd))]
    [arrowTE (a b) (arrowT (map (lambda (q) (parse-type q)) a)
                           (parse-type b))]
  )
)

(define (type-error tmfae msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string tmfae)
                      (string-append " not "
                                     msg)))))

;; inserts mapping from id to arguments to Env
;; listof Types list of symbols Env -> Env
(define (addEnv names param-types env)
  (if (not (empty? names))
      (aBind (first names) (first param-types) (addEnv (rest names) (rest param-types) env))
      env
  )
)

;; checks types of arguments with types of function parameters
;; list of types list of types
(define (checkApp params args)
    (if (empty? args)
        (and (empty? params) (empty? args))
        (local [(define p (first params))
                (define a (first args))]
            (and (type-case Type p
                    [anyT () true]
                    [else (type-case Type a
                            [anyT () true]
                            [crossT (la ra)
                                (type-case Type p
                                    [crossT (lp rp)
                                        (and (checkApp (list la) (list lp))
                                             (checkApp (list ra) (list rp))
                                        )]
                                    [else false]
                                )]
                            [arrowT (pa ra)
                                (type-case Type p
                                    [arrowT (pp rp)
                                        (and (checkApp pa pp)
                                             (checkApp (list ra) (list rp))
                                        )]
                                    [else false]
                                )]
                            [else (if (equal? p a) true false)]
                        )]
                )
                (checkApp (rest args) (rest params)))
        )
    )
)

(define (checkat args)
    (if (empty? args)
        false
        (type-case Type (first args)
            [anyT () true]
            [else (checkat (rest args))]
        )
    )
)

;; check two types
;; Type Type -> Type
(define (checktt a b error)
    (type-case Type a
        [anyT () 
            (type-case Type b
                [anyT () (anyT)]
                [else b]
            )]
        [else 
            (type-case Type b
                [anyT () a]
                [else 
                    (if (equal? a b)
                        a
                        (error))]
            )]
    )
)

(define typecheck : (TMFAE TypeEnv -> Type)
  (lambda (tmfae env)
    (type-case TMFAE tmfae
      [bool (val) (boolT)]
      [num (n) (numT)]
      [pair (fst snd) (crossT (typecheck fst env) (typecheck snd env))]
      [fst (val) (type-case Type (typecheck val env)
                    [anyT () (anyT)]
                    [crossT (fst snd) fst]
                    [else (type-error val "not a pair")]
                 )]
      [snd (val) (type-case Type (typecheck val env)
                    [anyT () (anyT)]
                    [crossT (fst snd) snd]
                    [else (type-error val "not a pair")]
                 )]
      [add (l r) (type-case Type (typecheck l env)
                    [anyT () (anyT)]
                    [numT ()
                         (type-case Type (typecheck r env)
                            [anyT () (anyT)]
                            [numT () (numT)]
                            [else (type-error r "num")])]
                    [else (type-error l "num")])]
      [sub (l r) (type-case Type (typecheck l env)
                    [anyT () (anyT)]
                    [numT ()
                         (type-case Type (typecheck r env)
                            [anyT () (anyT)]
                            [numT () (numT)]
                            [else (type-error r "num")])]
                    [else (type-error l "num")])]
      [id (name) (get-type name env)]
      [eq (l r) (type-case Type (typecheck l env)
                    [anyT () (anyT)]
                    [numT ()
                            (type-case Type (typecheck r env)
                                [anyT () (anyT)]
                                [numT () (boolT)]
                                [else (type-error r "bool")])]
                    [else (type-error l "bool")]
                )]
      [ifthenelse (cnd exprt exprf)
        (local [(define cndT   (typecheck cnd env))
                (define exprtT (typecheck exprt env))
                (define exprfT (typecheck exprf env))]
               (type-case Type cndT
                [anyT () (anyT)]
                [boolT ()
                        (checktt exprtT exprfT 
                         (lambda () (type-error ifthenelse "e1 type != e2 type")))]
                [else (type-error cndT "bool")])
        )]
      [fun (names te body)
        (local [(define param-types (map (lambda (q) (parse-type q)) te))]
          (arrowT param-types
                  (typecheck body (addEnv names param-types env)))
        )
      ]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [anyT () (anyT)]
             [arrowT (param-types result-type)
                      (if (checkApp param-types (map (lambda (q) (typecheck q env)) arg))
                         (if (checkat (map (lambda (q) (typecheck q env)) arg))
                           (anyT)
                           result-type
                         )
                         (type-error arg "bad arguments` types"))]
             [else (type-error fn "function")])]
      [with (names nametys inits body)
            (local [(define inits-types (map (lambda (q) (typecheck q env)) inits))]
                (if (checkApp (map (lambda (q) (parse-type q)) nametys) inits-types)    
                    (typecheck body (addEnv names inits-types env))
                    (type-error with "with arguments types mismatch")
                )
            )]
      [try1 (try-expr catch-exprs)
            (local [(define try-exprT (typecheck try-expr env))
                    (define catch-exprsT (typecheck catch-exprs env))]
                   (checktt try-exprT catch-exprsT
                     (lambda () (type-error try1 "expressions types mismatch")))
            )]
      [throw () (anyT)]
)))

;  ----------------------------------------

(define run : (TMFAE -> TMFAE-Value)
    (lambda (tmfae)
          (interp tmfae (mtSub) (lambda (x) x) (lambda () (error 'interp "unhandled")))))

(define eval : (TMFAE -> TMFAE-Value)
    (lambda (tmfae)
          (begin
                  (try (typecheck tmfae (mtEnv))
                                  (lambda () (error 'type-error "typecheck")))
                        (run tmfae))))

; ----------------------------------------

; ***********
; ** TESTS **
; ***********

(test (eval (add (num 10) (num 17))) (numV 27))
(test (eval (sub (num 10) (num 7))) (numV 3))
(test (eval (app (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (list (add (num 1) (num 17))))) (numV 30))

(test   (eval (app (fun (list 'x) (list (numTE))
                        (app (fun (list 'f) (list (arrowTE (list (numTE)) (numTE)))
                                  (add (app (id 'f) (list (num 1)))
                                       (app (fun (list 'x) (list (numTE))
                                                 (app (id 'f)
                                                      (list (num 2))))
                                            (list (num 3)))))
                             (list (fun (list 'y) (list (numTE))
                                  (add (id 'x) (id 'y))))))
                   (list (num 0)))
        )
        (numV 3))

(test/exn (eval (id 'x)) "type-error: typecheck")

(test (typecheck (num 10) (mtEnv)) (numT))
(test (typecheck (add (num 10) (num 17)) (mtEnv)) (numT))
(test (typecheck (sub (num 10) (num 7)) (mtEnv)) (numT))
(test (typecheck (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (mtEnv)) (arrowT (list (numT)) (numT)))
(test (typecheck (fun (list 'x) (list (numTE)) (fun (list 'y) (list (boolTE)) (id 'x))) (mtEnv)) (arrowT (list (numT)) (arrowT (list (boolT))  (numT))))
(test (typecheck (app (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (list (add (num 1) (num 17)))) (mtEnv)) (numT))

(test/exn (typecheck (app (num 1) (list (num 2))) (mtEnv)) "no type")
(test/exn (typecheck (add (fun (list 'x) (list (numTE)) (num 12)) (num 2)) (mtEnv)) "no type")

;; #1
;; given

(test (eval (eq (num 13)
                  (ifthenelse (eq (num 1) (add (num -1) (num 2)))
                              (num 12)
                              (num 13))))
      (boolV false))

(test (typecheck (eq (num 13)
                     (ifthenelse (eq (num 1) (add (num -1) (num 2)))
                                 (num 12)
                                 (num 13)))
                 (mtEnv))
      (boolT))
(test/exn (typecheck (add (num 1)
                          (ifthenelse (bool true)
                                      (bool true)
                                      (bool false)))
                     (mtEnv))
          "no type")

;; my
(test/exn   (eval   (app (fun (list 'x 'y) (list (boolTE) (numTE))
                      (eq (id 'x) (id 'y)))
                    (list (bool false) (num 3))))
        "type-error: typecheck")
(test/exn   (eval   (app (fun (list 'x 'y) (list (boolTE) (boolTE))
                      (eq (id 'x) (id 'y)))
                    (list (bool false) (bool true))))
        "type-error: typecheck")
(test   (eval   (app (fun (list 'x 'y) (list (numTE) (numTE))
                      (eq (id 'x) (id 'y)))
                (list (num 4) (num 3))))
        (boolV false))
(test   (eval   (app (fun (list 'x 'y) (list (boolTE) (boolTE))
                      (ifthenelse (id 'x) (num 1) (num 2)))
                (list (bool false) (bool true))))
        (numV 2))
(test   (eval   (app (fun (list 'x 'y) (list (boolTE) (boolTE))
                      (ifthenelse (id 'y) (num 1) (num 2)))
                (list (bool false) (bool true))))
        (numV 1))
(test   (eval   (app (fun (list 'x 'y) (list (numTE) (numTE))
                      (eq (id 'x) (id 'y)))
                (list (num 3) (num 3))))
        (boolV true))
(test   (eval   (app (fun (list 'x 'y) (list (numTE) (numTE))
                      (eq (id 'x) (id 'y)))
                (list (num 3) (add (num 1) (num 2)))))
        (boolV true))
(test   (eval   (ifthenelse (bool false) (num 3) (num 4)))
        (numV 4))
(test   (eval   (ifthenelse (bool true) (num 3) (num 4)))
        (numV 3))
(test/exn   (eval   (ifthenelse (num 3) (num 4) (num 5)))
        "type-error: typecheck")
(test/exn   (eval   (ifthenelse (bool false) (bool false) (num 5)))
        "type-error: typecheck")



;; #2
;; given
(test (eval (fst (pair (num 10) (num 8)))) (numV 10))
(test (eval (snd (pair (num 10) (num 8)))) (numV 8))
(test (typecheck (pair (num 10) (num 8)) (mtEnv)) (crossT (numT) (numT)))
(test (typecheck (add (num 1) (snd (pair (num 10) (num 8)))) (mtEnv)) (numT))
(test (typecheck (fun (list 'x) (list (crossTE (numTE) (boolTE)))
                      (ifthenelse (snd (id 'x)) (num 0) (fst (id 'x))))
                 (mtEnv))
      (arrowT (list (crossT (numT) (boolT))) (numT)))
(test/exn (typecheck (fst (num 10)) (mtEnv)) "no type")
(test/exn (typecheck (add (num 1) (fst (pair (bool false) (num 8)))) (mtEnv)) "no type")
(test/exn (typecheck (fun (list 'x) (list (crossTE (numTE) (boolTE)))
                          (ifthenelse (fst (id 'x)) (num 0) (fst (id 'x))))
                     (mtEnv))
          "no type")
;; my
(test (eval (app (fun (list 'x 'y) (list (crossTE (boolTE) (numTE)) (numTE))
                      (fst (id 'x)))
                 (list (pair (bool false) (num 3)) (num 2))))
      (boolV false))

(test/exn (eval (app (fun (list 'x 'y) (list (crossTE (boolTE) (numTE)) (numTE))
                      (fst (id 'x)))
                 (list (pair (num 5) (num 3)) (num 2))))
      "type-error: typecheck")


;; #3
;; given
(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app 
              (fun (list 'x 'y) (list (numTE) (numTE))
                (sub (id 'x) (id 'y)))
              (list (num 10) (num 20))))
      (numV -10))
(test (typecheck (app 
                    (fun (list 'x 'y) (list (numTE) (boolTE))
                      (id 'y))
                  (list (num 10) (bool false)))
            (mtEnv))
      (boolT))
(test/exn (typecheck (app 
                        (fun (list 'x 'y) (list (numTE) (boolTE))
                          (id 'y))
                        (list (num 10) (num 10)))
          (mtEnv))
  "no type")

(test (typecheck (throw) (mtEnv)) (anyT))
(test (typecheck (try1 (num 8) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 10)) (mtEnv)) (numT))
(test/exn (typecheck (try1 (num 8) (bool false)) (mtEnv)) "no type")

;; my
(test (run (app 
        (fun (list 'x 'y) (list (numTE) (numTE)) 
            (with (list 'x 'y) 
                  (list (numTE) (arrowTE (list (numTE)) (numTE))) 
                  (list 
                    (num 3)
                    (fun (list 'x) (list (boolTE)) 
                         (ifthenelse (eq (id 'x) (num 3))
                                (num 12)
                                (num 6)
                         )
                    )
                  )
                  (app (id 'y) (list (id 'x)))
        ))
        (list (num 5) (add (num 2) (num 3))))) (numV 12))

(test/exn (eval (app 
        (fun (list 'x 'y 'z) (list (numTE) (numTE) (boolTE)) 
            (with (list 'x 'y) 
                  (list (numTE) (arrowTE (list (numTE)) (numTE))) 
                  (list 
                    (num 3)
                    (fun (list 'x) (list (boolTE)) 
                         (ifthenelse (eq (id 'z) (num 3))
                                (num 12)
                                (num 6)
                         )
                    )
                  )
                  (app (id 'y) (list (id 'x)))
        ))
        (list (num 5) (num 1) (bool false)))) "type-error: typecheck")

;; try1 - throw
(test   (eval   (try1   (app  (fun (list 'x) (list (numTE))
                                (add (num 32)
                                     (try1  (throw)
                                            (id 'x))
                                ))
                            (list (num 10)))
                        (num 5))
                )
        (numV 42))

(test   (eval   (try1   (add (num 32) (throw))
                        (num 5)))
        (numV 5))

(test   (eval   (try1   (app  (fun (list 'x) (list (numTE))
                                (add (num 32)
                                     (try1  (throw)
                                            (throw))
                                ))
                            (list (num 10)))
                        (num 5))
                )
        (numV 5))

(test   (eval   (app (fun (list 'x) (list (arrowTE (list (numTE)) (numTE)))
                        (app (id 'x) (list (num 10))))
                     (list (fun (list 'x) (list (numTE))
                                (add (id 'x) (num 10)))
                     )
        ))
        (numV 20))

(test   (eval   (try1 (app (fun (list 'x) (list (arrowTE (list (numTE)) (numTE)))
                            (app (id 'x) (list (throw))))
                         (list (fun (list 'x) (list (numTE))
                                    (add (id 'x) (num 10)))
                         ))
                      (num 42)
        ))
        (numV 42))

(test   (eval   (try1 (app (fun (list 'x) (list (arrowTE (list (numTE)) (numTE)))
                            (app (id 'x) (list (num 11))))
                         (list (fun (list 'x) (list (numTE))
                                    (add (id 'x) (throw)))
                         ))
                      (num 42)
        ))
        (numV 42))


;; additional
(test/exn (eval (ifthenelse (bool true) (num 3) (bool false))) "type-error: typecheck")
(test/exn (eval (app (fun (list 'x) (list (numTE)) (id 'x)) (list (bool false)))) "type-error: typecheck")
(test/exn (eval (app (fun (list 'x 'y) (list (numTE) (boolTE)) (num 23))
                     (list (bool false) (num 3)))) "type-error: typecheck")
(test/exn (eval (app (fun (list 'x 'y) (list (numTE) (boolTE)) (num 23))
                     (list (bool false)))) "type-error: typecheck")
(test/exn (eval (app (fun (list 'x) (list (numTE)) (num 23))
                     (list (bool false) (num 3)))) "type-error: typecheck")

;; add tests
(test (typecheck (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 5) (num 6) (num 7)) 
                 (add (id 'x) (num 1))
                      ) (mtEnv)) (numT))
(test (typecheck (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 5) (num 6) (num 7)) 
                 (eq (id 'x) (num 1))
                      ) (mtEnv)) (boolT))
(test (typecheck (try1 (try1 (num 7) (throw)) (num 9)) (mtEnv)) (numT))
(test (run (fst (pair (num 10) (num 8))) ) (numV 10))
(test (run (snd (pair (num 10) (num 8))) ) (numV 8))
(test (typecheck (pair (num 10) (num 8)) (mtEnv)) (crossT (numT) (numT)))
(test (typecheck (add (num 1) (snd (pair (num 10) (num 8)))) (mtEnv)) (numT))
;
;(run (pair (num 10) (num 8)) )
(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE))
                        (sub (id 'x) (id 'y))) (list (num 10) (num 20))))
      (numV -10))
(test (run (with (list 'x) (list (numTE)) (list (num 5)) (add (id 'x) (id 'x)))) (numV 10))
(test (run (with (list 'x) (list (numTE)) (list (num 5)) 
                 (add (id 'x) (with (list 'x) (list (numTE)) (list (num 3)) (num 10))
                      ))) (numV 15))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                           (id 'y))
                      (list (num 10) (bool false)))
                 (mtEnv))
      (boolT))
(test/exn (typecheck (app (fun (list 'x 'y) (list (numTE) (boolTE))
                               (id 'y))
                          (list (num 10) (num 10)))
                     (mtEnv))
          "no type")
(test (typecheck (throw) (mtEnv)) (anyT))
(test (typecheck (try1 (num 8) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 10)) (mtEnv)) (numT))


;; TA TESTS
(test (typecheck (bool true) (mtEnv)) (boolT))
(test (typecheck (eq (num 2) (throw)) (mtEnv)) (boolT))
(test (typecheck (ifthenelse (bool false) (num 2) (throw)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (throw) (num 2)) (mtEnv)) (numT))
(test (typecheck (ifthenelse (bool false) (throw) (throw)) (mtEnv)) (anyT))
(test (typecheck (pair (num 2) (bool false)) (mtEnv)) (crossT (numT) (boolT)))
(test (typecheck (pair (num 2) (throw)) (mtEnv)) (crossT (numT) (anyT)))
(test (typecheck (snd (throw)) (mtEnv)) (anyT))
(test (typecheck (fst (pair (num 2) (bool false))) (mtEnv)) (numT))
(test (typecheck (snd (pair (num 2) (bool false))) (mtEnv)) (boolT))
(test (typecheck (fun empty empty (num 2)) (mtEnv)) (arrowT empty (numT)))
(test (typecheck (fun (list 'x) (list (numTE)) (throw)) (mtEnv)) (arrowT (list (numT)) (anyT)))
(test (typecheck (app (fun empty empty (num 2)) empty) (mtEnv)) (numT))
(test (typecheck (app (throw) (list (num 2) (bool false))) (mtEnv)) (anyT))
(test (typecheck (app (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y))) (list (num 2) (num 3))) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (num 2)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (throw)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'x 'y 'z) (list (boolTE) (numTE) (numTE)) (list (bool false) (num 2) (num 3)) (ifthenelse (id 'x) (id 'y) (id 'z))) (mtEnv)) (numT))
(test (typecheck (with empty empty empty (num 2)) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (throw)) (num 2)) (mtEnv)) (numT))
(test (run (eq (num 2) (num 3))) (boolV false))
(test (run (eq (num 2) (num 2))) (boolV true))
(test (run (ifthenelse (bool true) (num 2) (num 3))) (numV 2))
(test (run (ifthenelse (bool false) (num 2) (num 3))) (numV 3))
(test (run (with (list 'x 'y 'z) (list (numTE) (numTE) (numTE)) (list (num 2) (num 3) (num 4)) (add (id 'x) (id 'y)))) (numV 5))
(test (run (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y)))) (closureV (list 'x 'y) (add (id 'x) (id 'y)) (mtSub)))
(test (run (app (fun (list 'x 'y) (list (numTE) (numTE)) (add (id 'x) (id 'y))) (list (num 2) (num 3)))) (numV 5))
(test (run (fst (pair (num 2) (num 3)))) (numV 2))
(test (typecheck (sub (throw) (throw)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (throw)) (mtEnv)) (anyT))
(test (typecheck (app (throw) (list (num 1))) (mtEnv)) (anyT))
(test (typecheck (fst (throw)) (mtEnv)) (anyT))
(test (typecheck (ifthenelse (bool true) (fun (list 'x 'y) (list (numTE) (numTE)) (throw)) (fun (list 'z 'a) (list (numTE) (numTE)) (add (id 'z) (id 'a)))) (mtEnv)) (arrowT (list (numT) (numT)) (numT)))
(test (typecheck (try1 (num 2) (throw)) (mtEnv)) (numT))
(test (typecheck (try1 (throw) (num 2)) (mtEnv)) (numT))
(test (typecheck (try1 (num 2) (num 2)) (mtEnv)) (numT))
(test (typecheck (app (fun (list 'a) (list (numTE)) (add (throw) (num 10))) (list (throw))) (mtEnv)) (numT))
(test (typecheck (try1 (with (list 'map 'foo) (list (arrowTE (list (arrowTE (list (numTE)) (boolTE)) (crossTE (numTE) (numTE))) (crossTE (boolTE) (boolTE))) (crossTE (numTE) (numTE)))          (list (fun (list 'f 'p) (list (arrowTE (list (numTE)) (boolTE)) (crossTE (numTE) (numTE))) (pair (app (id 'f) (list (fst (id 'p)))) (app (id 'f) (list (snd (id 'p)))))) (pair (num 10) (num 42))) (app (id 'map) (list (throw) (id 'foo)))) (pair (bool false) (bool false))) (mtEnv))     (crossT (boolT) (boolT)))
(test (typecheck (try1 (pair (throw) (num 42)) (pair (bool false) (throw))) (mtEnv)) (crossT (boolT) (numT)))
(test (typecheck (try1 (add (throw) (num 8)) (num 10)) (mtEnv)) (numT))
(test (typecheck (try1 (pair (num 8) (num 2)) (throw)) (mtEnv)) (crossT (numT) (numT)))
(test (typecheck (eq (num 42) (try1 (ifthenelse (bool true) (throw) (throw)) (num 10))) (mtEnv)) (boolT))
(test (typecheck (ifthenelse (throw) (pair (throw) (num 42)) (pair (bool false) (throw))) (mtEnv)) (crossT (boolT) (numT)))
(test (typecheck (try1 (pair (throw) (num 42)) (pair (bool false) (throw))) (mtEnv)) (crossT (boolT) (numT)))
(test (typecheck (with (list 'x 'y 'z) (list (boolTE) (numTE) (numTE)) (list (bool false) (num 2) (num 3)) (ifthenelse (id 'x) (id 'y) (id 'z))) (mtEnv)) (numT))
(test (typecheck (with (list 'x) (list (numTE)) (list (num 2)) (id 'x)) (mtEnv)) (numT))
(test (typecheck (with (list 'dup) (list (arrowTE (list (numTE)) (crossTE (numTE) (numTE)))) (list (fun (list 'n) (list (numTE)) (pair (id 'n) (id 'n)))) (app (id 'dup) (list (throw)))) (mtEnv))   (crossT (numT) (numT)))
(test/exn (typecheck (app (throw) (list (add (bool true) (throw)))) (mtEnv)) "no type")
(test/exn (typecheck (app (throw) (list (ifthenelse (num 1) (num 2) (num 3)))) (mtEnv)) "no type")
(test/exn (typecheck (app (throw) (list (app (bool true) (list (throw))))) (mtEnv)) "no type")
