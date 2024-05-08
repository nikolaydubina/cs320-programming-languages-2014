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

(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))