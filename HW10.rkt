#lang plai-typed

(define-type TVRCFAE
  [num (n : number)]
  [bool (val : boolean)]
  [add (lhs : TVRCFAE)
       (rhs : TVRCFAE)]
  [sub (lhs : TVRCFAE)
       (rhs : TVRCFAE)]
  [id (name : symbol)]
  [if0 (test-expr : TVRCFAE)
      (then-expr : TVRCFAE)
      (else-expr : TVRCFAE)]
  [fun (params : (listof symbol))
       (paramtys : (listof TE))
       (body : TVRCFAE)]
  [app (fun-expr : TVRCFAE)
       (arg-exprs : (listof TVRCFAE))]
  [rec (id : symbol)
       (type : TE)
       (fun : TVRCFAE)
       (body : TVRCFAE)]
  [with-type (name : symbol)
             (var1-name : symbol) (var1-ty : TE)
             (var2-name : symbol) (var2-ty : TE)
             (body-expr : TVRCFAE)]
  [cases (name : symbol)
         (dispatch-expr : TVRCFAE)
         (var1-name : symbol) (bind1-name : symbol) (rhs1-expr : TVRCFAE)
         (var2-name : symbol) (bind2-name : symbol) (rhs2-expr : TVRCFAE)]
)


(define-type TE
  [numTE]
  [boolTE]
  [idTE (name : symbol)]
  [arrowTE (args : (listof TE))
           (result : TE)]
)

(define-type TVRCFAE-Value
    [numV (n : number)]
    [boolV (val : boolean)]
    [closureV 
        (params : (listof symbol))
        (body : TVRCFAE)
        (ds : DefrdSub)]
    [variantV (right? : boolean) (val : TVRCFAE-Value)]
    [constructorV (right? : boolean)]
)

(define-type DefrdSub
    [mtSub]
    [aSub 
        (name : symbol)
        (value : TVRCFAE-Value)
        (rest : DefrdSub)]
    [aRecSub 
        (name : symbol)
        (val-box :  (boxof TVRCFAE-Value))
        (rest : DefrdSub)]
)

(define-type Type
  [numT]
  [boolT]
  [idT (name : symbol)]
  [arrowT (param : (listof Type))
          (result : Type)]
)

(define-type TypeEnv
    [mtEnv]
    [aBind  (name : symbol)
            (type : Type)
            (rest : TypeEnv)
    ]
    [tBind  (name : symbol)
            (var1-name : symbol) (var1-type : Type)
            (var2-name : symbol) (var2-type : Type)
            (rest : TypeEnv)
    ]
)

; ----------------------------------------

(define (interp tvrcfae ds)
    (type-case TVRCFAE tvrcfae
        [bool (val) (boolV val)]
        [num (n) (numV n)]
        [add (l r) (num+ (interp l ds) (interp r ds))]
        [sub (l r) (num- (interp l ds) (interp r ds))]
        [id (name) (lookup name ds)]
        [if0 (test-expr then-expr else-expr)
             (if (isnumzero (numV-n (interp test-expr ds)))
               (interp then-expr ds)
               (interp else-expr ds))
        ]
        [rec (bound-id type named-expr body-expr)
             (local [(define value-holder (box (numV 42)))
                     (define new-ds (aRecSub bound-id value-holder ds))]
                    (begin
                      (set-box! value-holder (interp named-expr new-ds))
                      (interp body-expr new-ds)
                    )
             )
        ]
        [fun (params paramtys body)
             (closureV params body ds)]
        [app (fun-expr arg-expr)
             (local [(define fun-val (interp fun-expr ds))
                     (define arg-vals (map (lambda (q) (interp q ds)) arg-expr))]
                    (type-case TVRCFAE-Value fun-val
                               [closureV (params body ds)
                                         (interp body (linkds params arg-vals ds))]
                               [constructorV (right)
                                             (variantV right (first arg-vals))]
                               [else (error 'interp "not applicable")]
                    )
             )]
        [with-type (type-name var1-name var1-te
                              var2-name var2-te
                              body-expr)
                   (interp body-expr
                           (aSub var1-name
                                 (constructorV false)
                                 (aSub var2-name
                                       (constructorV true)
                                       ds)))]
        [cases (ty dispatch-expr
                   var1-name var1-id var1-rhs
                   var2-name var2-id var2-rhs)
               (type-case TVRCFAE-Value (interp dispatch-expr ds)
                          [variantV (right? val)
                                    (if (not right?)
                                      (interp var1-rhs (aSub var1-id val ds))
                                      (interp var2-rhs (aSub var2-id val ds)))]
                          [else (error 'interp "not a variant result")]
               )
        ]
    )
)

;; isnumzero: any -> bool
(define (isnumzero a)
  (if (equal? 0 a)
        true
        false
  )
)


;; linkds: params argvals ds -> newds
(define (linkds params argvals ds)
    (if (empty? params)
        ds
        (aSub (first params) (first argvals) (linkds (rest params) (rest argvals) ds))
    )
)

;; num-op : (number number -> number) -> (TVRCFAE-Value TVRCFAE-Value -> TVRCFAE-Value)
(define (num-op op x y)
  (numV (op (numV-n x) (numV-n y))))

(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))

;; lookup
(define (lookup name ds)
  (type-case DefrdSub ds
             [mtSub () (error 'lookup "free variable")]
             [aSub (sub-name val rest-ds)
                   (if (symbol=? sub-name name)
                     val
                     (lookup name rest-ds))
             ]
             [aRecSub (sub-name val-box rest-ds)
                      (if (symbol=? sub-name name)
                        (unbox val-box)
                        (lookup name rest-ds)
                      )
             ]
  )
)

;  ----------------------------------------

(define (find-type-id name-to-find env)
  (type-case TypeEnv env
             [mtEnv () (error 'get-type "free type name, so no type")]
             [aBind (name ty rest)
                    (find-type-id name-to-find rest)]
             [tBind (name var1-name var1-ty var2-name var2-ty rest)
                    (if (symbol=? name-to-find name)
                      env
                      (find-type-id name-to-find rest))]))

(define (validtype ty env)
  (type-case Type ty
             [numT () (mtEnv)]
             [boolT () (mtEnv)]
             [arrowT (a b) (begin (map (lambda (q) (validtype q env)) a)
                                  (validtype b env))]
             [idT (id) (find-type-id id env)]))

;; linkenv: names types env -> newenv
(define (linkenv names types env)
    (if (empty? names)
        env
        (aBind (first names) (first types) (linkenv (rest names) (rest types) env))
    )
)

;; checks types of arguments with types of function parameters
;; list of types list of types
(define (checkApp params args)
    (if (and (empty? args) (empty? params))
      true
      (if (or (empty? args) (empty? params))
        (error 'checkApp "nof arg ine nop")
        (and (equal? (first params) (first args))
           (checkApp (rest params) (rest args)))
      )
    )
)

(define (type-error TVRCFAE msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string TVRCFAE)
                      (string-append " not "
                                     msg)))))

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [idTE (name) (idT name)]
    [arrowTE (a b) (arrowT (map (lambda (q) (parse-type q)) a)
                           (parse-type b))]
  )
)

;; lookupenv
(define (lookupenv name env)
  (type-case TypeEnv env
             [mtEnv () (error 'lookupenv "free variable")]
             [aBind (tname ty rest)
                    (if (symbol=? tname name)
                        ty
                        (lookupenv name rest)
                    )
             ]
             [tBind (tname
                     var1-name var1-ty
                     var2-name var2-ty
                     rest)
                    (lookupenv name rest)
             ]
  )
)

(define typecheck : (TVRCFAE TypeEnv -> Type)
  (lambda (tvrcfae env)
    (type-case TVRCFAE tvrcfae
        [num (n) (numT)]
        [bool (val) (boolT)]
        [add (l r) (type-case Type (typecheck l env)
                      [numT ()
                           (type-case Type (typecheck r env)
                              [numT () (numT)]
                              [else (type-error r "num")])]
                      [else (type-error l "num")])]
        [sub (l r) (type-case Type (typecheck l env)
                      [numT ()
                           (type-case Type (typecheck r env)
                              [numT () (numT)]
                              [else (type-error r "num")])]
                      [else (type-error l "num")])]
        [id (name) (lookupenv name env)]
        [if0 (test-expr then-expr else-expr)
            (local [(define testT (typecheck test-expr env))
                    (define thenT (typecheck then-expr env))
                    (define elseT (typecheck else-expr env))]
                   (type-case Type testT
                       [numT ()
                             (if (equal? thenT elseT)
                               thenT
                               (error 'if0  "different types")
                             )]
                       [else (error 'if0 "cond is not a number")]
                    )
            )]
        [fun (names tes body)
             (local [(define param-types (map (lambda (q) (parse-type q)) tes))]
                    (begin
                      (map (lambda (q) (validtype q env)) param-types)
                      (arrowT param-types
                              (typecheck body (linkenv names param-types env)))
                    )
             )
        ]
        [app (fun-expr arg-exprs)
             (local [(define fun-exprT (typecheck fun-expr env))
                     (define arg-types (map (lambda (q) (typecheck q env)) arg-exprs))]
                (type-case Type fun-exprT
                    [arrowT (param-types result-type)
                          (if (checkApp arg-types param-types)
                             result-type
                             (error 'app "bad arguments` types"))]
                    [else (error 'app "wrong args app")])
             )
        ]
        [rec (name ty rhs-expr body-expr)
             (local [(define rhs-ty (parse-type ty))
                     (define new-env (aBind name rhs-ty env))]
                    (if (equal? rhs-ty (typecheck rhs-expr new-env))
                      (typecheck body-expr new-env)
                      (type-error rhs-expr (to-string rhs-ty))
                    )
             )
        ]
        [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
                   (local [(define var1-ty (parse-type var1-te))
                           (define var2-ty (parse-type var2-te))
                           (define new-env (tBind type-name
                                                  var1-name var1-ty
                                                  var2-name var2-ty env))]
                          (begin
                            (validtype var1-ty new-env)
                            (validtype var2-ty new-env)
                            (typecheck body-expr
                                       (aBind var1-name
                                              (arrowT (list var1-ty) (idT type-name))
                                              (aBind var2-name
                                                     (arrowT (list var2-ty) (idT type-name))
                                                     new-env)
                                       )
                            )
                          )
                    )
        ]
        [cases (type-name dispatch-expr 
                var1-name var1-id var1-rhs 
                var2-name var2-id var2-rhs)
               (local [(define bind (find-type-id type-name env))]
                      (if (and (equal? var1-name (tBind-var1-name bind))
                               (equal? var2-name (tBind-var2-name bind)))
                        (type-case Type (typecheck dispatch-expr env)
                                   [idT (name)
                                        (if (equal? name type-name)
                                          (local [(define rhs1-ty
                                                    (typecheck var1-rhs
                                                               (aBind var1-id (tBind-var1-type bind) env)))
                                                  (define rhs2-ty
                                                    (typecheck var2-rhs
                                                               (aBind var2-id (tBind-var2-type bind) env)))]
                                                 (if (equal? rhs1-ty rhs2-ty)
                                                   rhs1-ty
                                                   (type-error var2-rhs (to-string rhs1-ty))))
                                          (type-error dispatch-expr (to-string type-name)))]
                                   [else (type-error dispatch-expr (to-string type-name))])
                        (type-error tvrcfae "matching variant names")))]
    )
  )
)

;  ----------------------------------------

(define run : (TVRCFAE -> TVRCFAE-Value)
    (lambda (TVRCFAE)
          (interp TVRCFAE (mtSub)))
)

(define eval : (TVRCFAE -> TVRCFAE-Value)
    (lambda (TVRCFAE)
          (begin
                (typecheck TVRCFAE (mtEnv))
                (run TVRCFAE)
          )
    )
)

; ----------------------------------------

; ***********
; ** TESTS **
; ***********

;; from HW9.rkt
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

(test (typecheck (num 10) (mtEnv)) (numT))
(test (typecheck (add (num 10) (num 17)) (mtEnv)) (numT))
(test (typecheck (sub (num 10) (num 7)) (mtEnv)) (numT))
(test (typecheck (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (mtEnv)) (arrowT (list (numT)) (numT)))
(test (typecheck (app (fun (list 'x) (list (numTE)) (add (id 'x) (num 12))) (list (add (num 1) (num 17)))) (mtEnv)) (numT))

(test/exn (typecheck (app (num 1) (list (num 2))) (mtEnv)) "app: wrong args app")
(test/exn (typecheck (add (fun (list 'x) (list (numTE)) (num 12)) (num 2)) (mtEnv)) "no type")

(test (run (app (fun (list) (list) (num 10)) (list))) (numV 10))
(test (run (app 
              (fun (list 'x 'y) (list (numTE) (numTE))
                (sub (id 'x) (id 'y)))
              (list (num 10) (num 20))))
      (numV -10))

(test (eval (if0  (sub (num 4) (num 4))
                  (num 42)
                  (num 10)
      )) (numV 42))

(test (eval (if0  (sub (num 4) (num 3))
                  (num 42)
                  (num 10)
      )) (numV 10))

(test (eval
        (rec 'x (arrowTE (list (numTE)) (numTE))
          (fun (list 'y) (list (numTE))
            (if0 (sub (id 'y) (num 1))
              (id 'y)
              (add (num 2) (app (id 'x) (list (sub (id 'y) (num 1)))))
            ))
          (app (id 'x) (list (num 10)))
        ))
      (numV 19))

(test (eval
        (app (fun (list 'z) (list (numTE))
            (rec 'x (arrowTE (list (numTE)) (numTE))
              (fun (list 'y) (list (numTE))
                (if0 (sub (id 'y) (num 1))
                  (id 'y)
                  (add (id 'z) (app (id 'x) (list (sub (id 'y) (num 1)))))
                ))
              (app (id 'x) (list (num 10)))
            ))
            (list (num 10)))
      )
      (numV 91))

(test (eval (bool false)) (boolV false))

(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (app (id 'v1) (list (num 42)))
            )
        )
        (variantV #f (numV 42))
)
(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (app (id 'v2) (list (bool false)))
            )
        )
        (variantV #t (boolV false))
)
(test/exn (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (app (id 'v2) (list (num 3)))
            )
        )
        "app: bad arguments` types"
)

(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (cases 't1 (app (id 'v1) (list (num 2)))
                    'v1 'x (add (id 'x) (num 1))
                    'v2 'y (num 2)
                )
            )
        )
        (numV 3)
)
(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (cases 't1 (app (id 'v2) (list (bool false)))
                    'v1 'x (add (id 'x) (num 1))
                    'v2 'y (num 2)
                )
            )
        )
        (numV 2)
)

(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (app
                  (fun (list 'x) (list (idTE 't1)) (num 10))
                  (list (app (id 'v1) (list (num 5))))
                )
            )
        )
        (numV 10)
)
(test   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (with-type 'q1 'z1 (boolTE)
                               'z2 (numTE)
                    (app (id 'v1) (list (num 42)))
                )
            )
        )
        (variantV #f (numV 42))
)
;; additional

(test/exn (eval (if0 (num 0) (num 3) (fun (list 'x) (list (numTE)) (id 'x)))) "if0: different types")
(test/exn (eval (if0 (bool false) (num 3) (fun (list 'x) (list (numTE)) (id 'x)))) "if0: cond is not a number")
(test/exn (eval (app (fun (list 'x 'y) (list (numTE) (numTE)) (num 23))
                     (list (fun (list 'x) (list (numTE)) (num 10)) (num 3)))) "app: bad arguments` types")
(test/exn (eval (app (fun (list 'x 'y) (list (numTE) (numTE)) (num 23))
                     (list (num 10)))) "nof arg ine nop")

(test/exn (interp (id 'x) (mtSub)) "lookup: free variable")
(test/exn (eval (id 'x)) "lookupenv: free variable")
(test/exn (interp (app (num 3) (list (num 3))) (mtSub)) "not applicable")
(test/exn (interp
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (cases 't1 (num 3)
                       'v1 'x (num 1)
                       'v2 'y (num 2)
                )
            )
            (mtSub)
        )
        "interp: not a variant result"
)
(test/exn (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (cases 't2 (num 3)
                       'v1 'x (num 1)
                       'v2 'y (num 2)
                )
            )
        )
        "get-type: free type name, so no type"
)
(test/exn (eval
                (cases 't1 (num 3)
                       'v1 'x (num 1)
                       'v2 'y (num 2)
                )
        )
        "get-type: free type name, so no type"
)
(test/exn (eval (add (num 3) (bool false))) "typecheck: no type: (bool #f) not num")
(test/exn (eval (add (bool false) (num 2))) "typecheck: no type: (bool #f) not num")
(test/exn (eval (sub (num 3) (bool false))) "typecheck: no type: (bool #f) not num")
(test/exn (eval (sub (bool false) (num 2))) "typecheck: no type: (bool #f) not num")

(test/exn (eval
        (rec 'x (arrowTE (list (boolTE)) (numTE))
          (fun (list 'y) (list (numTE))
            (if0 (sub (id 'y) (num 1))
              (id 'y)
              (add (num 2) (app (id 'x) (list (bool false))))
            ))
          (app (id 'x) (list (bool false)))
        ))
      "typecheck: no type: (fun '(y) (list (numTE)) (if0 (sub (id 'y) (num 1)) (id 'y) (add (num 2) (app (id 'x) (list (bool #f)))))) not (arrowT (list (boolT)) (numT))")

(test (eval
        (rec 'x (arrowTE (list (numTE)) (numTE))
          (fun (list 'y) (list (numTE))
            (if0 (sub (id 'y) (num 1))
              (id 'y)
              (add (num 2) (app (id 'x) (list (sub (id 'y) (num 1)))))
            ))
          (app (id 'x) (list (num 10)))
        ))
      (numV 19))

(test/exn   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (with-type 'q1 'z1 (boolTE)
                               'z2 (numTE)
                    (cases 't1 (app (id 'v2) (list (bool false)))
                        'v1 'x (num 1)
                        'z2 'y (num 2)
                    )
                )
            )
        )
        "typecheck: no type: (cases 't1 (app (id 'v2) (list (bool #f))) 'v1 'x (num 1) 'z2 'y (num 2)) not matching variant names"
)
(test/exn   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (with-type 'q1 'z1 (boolTE)
                               'z2 (numTE)
                    (cases 't1 (app (id 'v2) (list (bool false)))
                        'v1 'x (bool false)
                        'v2 'y (num 2)
                    )
                )
            )
        )
        "typecheck: no type: (num 2) not (boolT)"
)
(test/exn   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (with-type 'q1 'z1 (boolTE)
                               'z2 (numTE)
                    (cases 't1 (num 10)
                        'v1 'x (bool false)
                        'v2 'y (num 2)
                    )
                )
            )
        )
        "typecheck: no type: (num 10) not 't1"
)
(test/exn   (eval
            (with-type 't1 'v1 (numTE)
                           'v2 (boolTE)
                (with-type 'q1 'z1 (boolTE)
                               'z2 (numTE)
                    (cases 't1 (app (id 'z1) (list (bool false)))
                        'v1 'x (bool false)
                        'v2 'y (num 2)
                    )
                )
            )
        )
        "typecheck: no type: (app (id 'z1) (list (bool #f))) not 't1"
)
