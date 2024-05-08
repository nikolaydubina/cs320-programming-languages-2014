#lang plai-typed

(define-type TPFAE
  [num (n : number)]
  [add (lhs : TPFAE) (rhs : TPFAE)]
  [sub (lhs : TPFAE) (rhs : TPFAE)]
  [id (name : symbol)]
  [fun (param : symbol) (paramty : TE) (body : TPFAE)]
  [app (fun-expr : TPFAE) (arg-expr : TPFAE)]
  [if0 (test-expr : TPFAE) (then-expr : TPFAE) (else-expr : TPFAE)]
  [tfun (name : symbol) (expr : TPFAE)]
  [tapp (body : TPFAE) (type : TE)]
)

(define-type TE
  [numTE]
  [arrowTE (param : TE) (result : TE)]
  [polyTE (forall : symbol) (body : TE)]
  [tvTE (name : symbol)]
)

(define-type Type
  [numT]
  [arrowT (param : Type) (result : Type)]
  [polyT (forall : symbol) (body : Type)]
  [tvT (name : symbol)]
)

(define-type TPFAE-Value
  [numV (n : number)]
  [closureV (param : symbol) (body : TPFAE) (ds : DefrdSub)]
)

(define-type DefrdSub
    [mtSub]
    [aSub (name : symbol)
          (value : TPFAE-Value)
          (rest : DefrdSub)]
)

; ----------------------------------------

;; isnumzero: any -> bool
(define (isnumzero a)
  (if (equal? 0 a)
        true
        false
  )
)

;; num-op : (number number -> number) -> (TPFAE-Value TPFAE-Value -> TPFAE-Value)
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
  )
)

(define (interp tpfae ds)
    (type-case TPFAE tpfae
        [num (n) (numV n)]
        [add (l r) (num+ (interp l ds) (interp r ds))]
        [sub (l r) (num- (interp l ds) (interp r ds))]
        [id (name) (lookup name ds)]
        [if0 (test-expr then-expr else-expr)
            (if (isnumzero (numV-n (interp test-expr ds)))
                (interp then-expr ds)
                (interp else-expr ds)
            )]
        [fun (param paramty body)
            (closureV param body ds)]
        [app (fun-expr arg-expr)
            (local [(define fun-val (interp fun-expr ds))
                        (define arg-val (interp arg-expr ds))]
                (type-case TPFAE-Value fun-val
                    [closureV (c-param c-body c-ds)
                        (interp c-body (aSub c-param arg-val c-ds))]
                    [else (error 'app "required closureV")]
                )
            )]
        [tfun (name expr)
            (interp expr ds)]
        [tapp (body type)
            (interp body ds)]
    )
)
;  ----------------------------------------

(define-type TypeEnv
    [mtEnv]
    [aBind  (name : symbol)
            (type : Type)
            (rest : TypeEnv)]
    [tBind  (name : symbol)
            (type : Type)
            (rest : TypeEnv)]
)

(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [arrowTE (a b) (arrowT (parse-type a)
                           (parse-type b))]
    [polyTE (forall body) (polyT forall (parse-type body))]
    [tvTE (name) (tvT name)]
  )
)

(define (lookupenv_a name env)
  (type-case TypeEnv env
             [mtEnv () (error 'lookupenv_a "free")]
             [aBind (tname ty rest)
                    (if (symbol=? tname name)
                        ty
                        (lookupenv_a name rest)
                    )]
             [tBind (tname ty rest) (lookupenv_a name rest)]
  )
)

(define (lookupenv_t name env)
  (type-case TypeEnv env
             [mtEnv () (error 'lookupenv_t "free")]
             [aBind (tname ty rest) (lookupenv_t name rest)]
             [tBind (tname ty rest)
                    (if (symbol=? tname name)
                        ty
                        (lookupenv_t name rest)
                    )]
  )
)

(define (findenv_t name env)
  (type-case TypeEnv env
             [mtEnv () #f]
             [aBind (tname ty rest) (findenv_t name rest)]
             [tBind (tname ty rest)
                    (if (symbol=? tname name)
                        #t
                        (findenv_t name rest)
                    )]
  )
)

(define (validtype ty env)
  (type-case Type ty
        [numT () (mtEnv)]
        [arrowT (a b) (begin (validtype a env)
                             (validtype b env))]
        [polyT (forall body) (validtype body (tBind forall (tvT forall) env))]
        [tvT (name) (if (findenv_t name env)
                      (mtEnv)
                      (error 'valid "free"))]
  )
)

(define (type-error TPFAE msg)
  (error 'typecheck (string-append
                     "no type: "
                     (string-append
                      (to-string TPFAE)
                      (string-append " not "
                                     msg)))))

(define (unpack atype env)
  (type-case Type atype
        [numT () (numT)]
        [arrowT (a b) (arrowT (unpack a env)
                              (unpack b env))]
        [polyT (forall body) 
            (polyT forall 
                (unpack body (tBind forall (tvT forall) env))
            )]
        [tvT (name) (lookupenv_t name env)]
  )
)

(define typecheck : (TPFAE TypeEnv -> Type)
  (lambda (tpfae env)
    (type-case TPFAE tpfae
        [num (n) (numT)]
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
        [id (name) (lookupenv_a name env)]
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
        [fun (name tes body)
             (local [(define param-type (parse-type tes))]
                    (begin
                      (validtype param-type env)
                      (arrowT param-type
                              (typecheck body (aBind name param-type env)))
                    )
             )]
        [app (fun-expr arg-expr)
             (local [(define fun-exprT (typecheck fun-expr env))
                     (define arg-type  (typecheck arg-expr env))]
                (type-case Type fun-exprT
                    [arrowT (param-type result-type)
                          (if (equal? arg-type param-type)
                             result-type
                             (error 'app "bad arguments` types"))]
                    [else (error 'app "wrong args app")])
             )]
        [tfun (name expr) 
            (polyT name (typecheck expr (tBind name (tvT name) env)))]
        [tapp (body type) 
             (local [(define body-t (typecheck body env))
                     (define type-t (parse-type type))]
                (type-case Type body-t
                    [polyT (forall fbody)
                        (unpack fbody (tBind forall type-t env))]
                    [else (error 'tapp "no")]
                )
             )]
    )
  )
)


;; -----------
;; -- TESTS --
;; -----------

;; given
(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))
 
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))
 
(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
 
(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha)))
                                         (polyT 'alpha (polyT 'beta (tvT 'alpha)))))))

(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv)) (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv)) (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

(test/exn (typecheck (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'beta))) (id 'x)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (id 'f) (numTE)) (aBind 'f (arrowT (numT) (numT)) (mtEnv))) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (numTE)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (tfun 'beta (fun 'y (tvTE 'beta) (add (id 'x) (id 'y)))))) (mtEnv)) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))
