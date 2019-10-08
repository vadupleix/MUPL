;;A MUPL language built using the following Racket built-in types and their functions:
;;--int, real, string, array
;;and following built-in functions:
;;--if

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for MUPL programs - Do NOT change
;; primitive types, string, number, etc
(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct int  (num)    #:transparent)  ;; a constant number, e.g., (int 17)
(struct real (num)    #:transparent) ;; a constant float number, int gets coerced to real when necessary.
(struct string (str)  #:transparent) ;; string

;; arithmatic between primitive types
(struct add  (e1 e2)  #:transparent)  ;; add two expressions
(struct isgreater (e1 e2)    #:transparent) ;; if e1 > e2 then 1 else 0

;; logic operators

;; if, cond, loop
(struct ifnz (e1 e2 e3) #:transparent) ;; if not zero e1 then e2 else e3

;; functions
(struct fun  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct call (funexp actual)       #:transparent) ;; function call

;; bindings
(struct mlet (var e body) #:transparent) ;; a local binding (let var = e in body)

;; data structures
(struct apair   (e1 e2) #:transparent) ;; make a new pair
(struct first   (e)     #:transparent) ;; get first part of a pair
(struct second  (e)     #:transparent) ;; get second part of a pair

(struct llist   (e)     #:transparent) ;; linked list (llist (apair e))
(struct arr     (e)     #:transparent) ;; fixed-length array
(struct alist   (e)     #:transparent) ;; dynamic array 
(struct index   (e index) #:transparent) ;;get the index'th element of the list

(struct hashset (e)     #:transparent) ;; hashset

(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e)     #:transparent) ;; if e1 is unit then 1 else 0

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env fun) #:transparent) 

;; lookup a variable in an environment
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(equal? (car (car env)) str) (cdr (car env))]
        [#t (envlookup (cdr env) str)]))


;; Helper function used for testing propose

(define (racketlist->mupllist rkt-list)
  (if (null? rkt-list) (munit) (apair (car rkt-list) (racketlist->mupllist (cdr rkt-list)))))
                                       
(define (mupllist->racketlist mp-list)
  (if (munit? mp-list) null (cons (apair-e1 mp-list) (mupllist->racketlist (apair-e2 mp-list)))))


(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars exp)
  (letrec ([set-builder (lambda (e)
                          (cond [(fun? e)
                                 (let* ([f-name (fun-nameopt e)]
                                        [f-arg (fun-formal e)]
                                        [f-body (fun-body e)]
                                        [body-set (set-remove (set-builder f-body) f-arg)])
                                   (if (null? f-name)
                                       body-set
                                       (set-remove body-set f-name)))]
                                [(var? e) (set (var-string e))]
                                [(int? e) (set )]
                                [(real? e) (set )]
                                [(string? e) (set )]
                                [(add? e) (set-union (set-builder (add-e1 e)) (set-builder (add-e2 e)))]
                                [(isgreater? e)
                                 (let ([v1 (isgreater-e1 e)]
                                       [v2 (isgreater-e2 e)])
                                   (set-union (set-builder v1) (set-builder v2)))]
                                [(ifnz? e)
                                 (let ([v1 (ifnz-e1 e)]
                                       [v2 (ifnz-e2 e)]
                                       [v3 (ifnz-e3 e)])
                                   (set-union (set-builder v1) (set-builder v2) (set-builder v3)))]
                                ;[(closure? ;don't expect to encounter closures because this function is called before eval
                                [(mlet? e)
                                 (let ([v1 (mlet-e e)]
                                       [v2 (mlet-body e)])
                                   (set-union (set-builder v1) (set-remove (set-builder v2) (mlet-var e))))]
                                [(call? e)
                                 (let ([v (call-funexp e)]
                                       [v2 (call-actual e)])
                                   (set-union (set-builder v) (set-builder v2)))]
                                [(apair? e)
                                 (let ([v1 (apair-e1 e)]
                                       [v2 (apair-e2 e)])
                                   (set-union (set-builder v1) (set-builder v2)))]
                                [(first? e)
                                 (let ([v (first-e e)])
                                   (set-builder v))]
                                [(second? e)
                                 (let ([v (second-e e)])
                                   (set-builder v))]
                                [(ismunit? e)
                                 (let ([v (ismunit-e e)])
                                   (set-builder v))]
                                [(munit? e) (set )]
                                [#t (error (format "bad MUPL expression: ~v" e))]))])
    (cond [(fun? exp) (fun-challenge (fun-nameopt exp) (fun-formal exp) (compute-free-vars (fun-body exp)) (set-builder exp))]
          [(var? exp) exp]
          [(int? exp) exp]
          [(real? exp) exp]
          [(string? exp) exp]
          [(add? exp) (add (compute-free-vars (add-e1 exp)) (compute-free-vars (add-e2 exp)))]
          [(isgreater? exp) (isgreater (compute-free-vars (isgreater-e1 exp)) (compute-free-vars (isgreater-e2 exp)))]
          [(ifnz? exp) (ifnz (compute-free-vars (ifnz-e1 exp)) (compute-free-vars (ifnz-e2 exp)) (compute-free-vars (ifnz-e3 exp)))]
          ;[(closure? e) e] ;don't expect to encounter closures because this function is called before eval
          [(mlet? exp) (mlet (mlet-var exp) (compute-free-vars (mlet-e exp)) (compute-free-vars (mlet-body exp)))]
          [(call? exp) (call (compute-free-vars (call-funexp exp)) (compute-free-vars (call-actual exp)))]
          [(apair? exp) (apair (compute-free-vars (apair-e1 exp)) (compute-free-vars (apair-e2 exp)))]
          [(first? exp) (first (compute-free-vars (first-e exp)))]
          [(second? exp) (second (compute-free-vars (second-e exp)))]
          [(ismunit? exp) (ismunit (compute-free-vars (ismunit-e exp)))]
          [(munit? exp) exp]
          [#t (error (format "bad MUPL expression: ~v" exp))])))


(define (eval-under-env e env)
    (cond [(var? e) 
           (envlookup env (var-string e))]
          [(int? e) e]
          [(real? e) e]
          [(string? e) e]
          [(add? e)
           (let ([v1 (eval-under-env (add-e1 e) env)]
                 [v2 (eval-under-env (add-e2 e) env)])
             (cond [(and (int? v1) (int? v2)) (int (+ (int-num v1) (int-num v2)))]
                   [(and (real? v1) (int? v2)) (real (+ (real-num v1) (int-num v2)))]
                   [(and (int? v1) (real? v2)) (real (+ (int-num v1) (real-num v2)))]
                   [(and (real? v1) (real? v2)) (real (+ (real-num v1) (real-num v2)))]
                   [(and (string? v1) (string? v2)) (string (string-append (string-str v1) (string-str v2)))]
                   [(string? v1) (let ([v2str
                                   (cond [(real? v2) (number->string (real-num v2))]
                                         [(int? v2) (number->string (int-num v2))]
                                         [#t (error "string has be added to a number or string")])])
                                   (string (string-append (string-str v1) v2str)))]
                   [(string? v2) (let ([v1str
                                   (cond [(real? v1) (number->string (real-num v1))]
                                         [(int? v1) (number->string (int-num v1))]
                                         [#t (error "string has be added to a number or string")])])
                                   (string (string-append v1str (string-str v2))))]
                   [#t (error "MUPL addition applied to non-number")]))] 
          [(isgreater? e)
           (let ([v1 (eval-under-env (isgreater-e1 e) env)]
                 [v2 (eval-under-env (isgreater-e2 e) env)])
             (if (and (int? v1)
                      (int? v2))
                 (if (> (int-num v1) (int-num v2)) (int 1) (int 0))
                 (error "MUPL isgreater applied to float or non-number")))]
          [(ifnz? e)
           (let ([v (eval-under-env (ifnz-e1 e) env)])
             (if (and (int? v))
                 (if (= (int-num v) 0)
                     (eval-under-env (ifnz-e3 e) env)
                     (eval-under-env (ifnz-e2 e) env))
                 (error "MUPL ifnz applied to non-integer")))]
          [(fun? e)
           (error "Don't expect fun here -- for testing only")]
          [(fun-challenge? e)
           (let* ([freevar (fun-challenge-freevars e)]
                 [env-map (lambda (str) (cons str (envlookup env str)))]
                 [env-local (set->list (set-map freevar env-map))])
             (closure env-local e))]
          [(closure? e) e]
          [(mlet? e)
           (let ([v-name (mlet-var e)])
             (if (string? v-name)
                 (let*
                     ([v (eval-under-env (mlet-e e) env)]
                      [env-local (cons (cons v-name v) env)])
                   (eval-under-env (mlet-body e) env-local))
                 (error "var in mlet var e body not a valid variable name")))]
          [(call? e)
           (let ([cl (eval-under-env (call-funexp e) env)])
             (if (closure? cl)
                 (let* ([f (closure-fun cl)]
                        [arg (eval-under-env (call-actual e) env)]
                        [envir (cons (cons (fun-challenge-formal f) arg) (closure-env cl))]
                        [f-name (fun-challenge-nameopt f)])
                   (if (null? f-name)
                       (eval-under-env (fun-challenge-body f) envir)
                       (let ([envir-rec (cons (cons f-name cl) envir)])
                         (eval-under-env (fun-challenge-body f) envir-rec))))
                 (error "a function closure expected in the first argument of call")))]
          [(apair? e)
           (let ([first-arg (eval-under-env (apair-e1 e) env)]
                 [second-arg (eval-under-env (apair-e2 e) env)])
             (if (munit? first-arg)
                 (error "first argument of apair cannot be (munit)")
                 (apair first-arg second-arg)))]
          [(first? e)
           (let ([pr (eval-under-env (first-e e) env)])
             (if (apair? pr)
                 (apair-e1 pr)
                 (error "first applied to non-pair")
                 ))]
          [(second? e)
           (let ([pr (eval-under-env (second-e e) env)])
             (if (apair? pr)
                 (apair-e2 pr)
                 (error "second applied to non-pair")
                 ))]
          [(ismunit? e)
           (let ([e1 (eval-under-env (ismunit-e e) env)])
             (if (munit? e1)
                 (int 1)
                 (int 0)))]
          [(munit? e) e]
          [#t (error (format "bad MUPL expression: ~v" e))]))


(define (eval-exp e)
  (eval-under-env (compute-free-vars e) null))


;; "Macos"

(define (ifmunit e1 e2 e3) (ifnz (ismunit e1) e2 e3))

(define (mlet* bs e2) (if (null? bs)
                          e2
                          (mlet (caar bs) (cdr (car bs)) (mlet* (cdr bs) e2))))

(define (ifeq e1 e2 e3 e4) (mlet* (list (cons "e1" e1) (cons "e2" e2)) (ifnz (isgreater (var "e1") (var "e2")) e4
                                 (ifnz (isgreater (var "e2") (var "e1"))
                                       e4
                                       e3))))

;; Problem 4

(define mupl-filter
  (fun "f-out" "f"
       (fun "f-in" "xs" 
            (ifnz (ismunit (var "xs"))
                  (var "xs")
                  (mlet "tail" (call (var "f-in") (second (var "xs")))
                        (ifnz (call (var "f") (first (var "xs")))
                              (apair (first (var "xs")) (var "tail"))
                              (var "tail")))))))

(define mupl-all-gt
  (mlet "filter" mupl-filter
        (fun "f-main" "int"
             (mlet "filter-fun"
                   (fun null "x"
                        (isgreater (var "x") (var "int")))
                   (fun "f-in" "xs"
                        (call (call (var "filter") (var "filter-fun")) (var "xs")))))))
                  

;; Test
(define f (fun "g" "x" (ifnz (var "x") (add (var "x") (int 1)) (add (var "x") (int -1)))))
(define test-pair (apair f (int 2)))
(define test-list (apair (int 1) (apair (int 2) (apair (int 3) (apair (int 4) (apair (int 5) (munit)))))))
(define test-exp-easy (mlet "x" (int 2)
                       (mlet "y" (int 3)
                             (mlet "f-add"
                                   (fun "f" "xs"
                                        (ifnz (ismunit (var "xs"))
                                              (var "xs")
                                              (apair (int 0) (munit))
                                              )
                                        )
                                   (call (var "f-add") test-list))))) 
(define test-exp (mlet "x" (int 2)
                       (mlet "y" (int 3)
                             (mlet "f-add"
                                   (fun "f" "xs"
                                        (ifnz (ismunit (var "xs"))
                                              (var "xs")
                                              (apair (add (first (var "xs")) (var "y")) (call (var "f") (second (var "xs"))))
                                              )
                                        )
                                   (call (var "f-add") test-list)))))

(define test-exp-mlet* (mlet* (list (cons "x" (int 2)) (cons "y" (int 3)) (cons "f-add"
                                   (fun "f" "xs"
                                        (ifnz (ismunit (var "xs"))
                                              (var "xs")
                                              (apair (add (add (first (var "xs")) (var "y")) (var "x")) (call (var "f") (second (var "xs"))))
                                              )
                                        )))
                                   (call (var "f-add") test-list)))

(define test-filter-fun (fun "f" "x" (add (var "x") (int -3))))
(define test-filter-fun2 (fun "f" "x" (isgreater (int 5) (var "x"))))
(define test-filter-fun3 (fun "f" "x" (isgreater (int -1) (var "x"))))

