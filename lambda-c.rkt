#lang racket

(require redex "base.rkt")

;; ----------------------------------------------------------------------------
;; Syntax for λc

(define-extended-language λc base
  (T .... B)
  (t .... (c l l))
  (v .... (c l l) ((c ↦ c l l) v))
  (c {x : B t} (c ↦ c)))

;; ----------------------------------------------------------------------------
;; Operational semantics for λc

(define ->λc
  (extend-reduction-relation
   ->base λc
   [--> ((((c_1 ↦ c_2) l_p l_n) v_1) v_2)
        ((c_2 l_p l_n) (v_1 ((c_1 l_n l_p) v_2)))
        "CDecomp"]
   [--> (({x : B t} l_p l_n) k)
        ({x : B t} (subst x k t) k l_p)
        "CCheck"]
   [--> (in-hole E t_1) (in-hole E t_2)
        (where (t_2) ,(apply-reduction-relation ->λc (term t_1)))
        "Compat"]))

;; ----------------------------------------------------------------------------
;; Typing rules for λc

(define-extended-judgment-form λc ⊢base
  #:mode (⊢ I I O)
  #:contract (⊢ Γ t T)
  
  [(⊢c c T)
   ------------------------------- "Contract"
   (Γ . ⊢ . (c l_p l_n) (T -> T))]
  
  [(() . ⊢ . k B)
   (() . ⊢ . t_2 Bool)
   (⊢c {x : B t_1} B)
   (side-condition
    (t_2 . ⊃ . (subst x k t_1)))
   ----------------------------------- "Checking"
   (() . ⊢ . ({x : B t_1} t_2 k l) B)])

(define-judgment-form λc
  #:mode (⊢c I O)
  #:contract (⊢c c T)
  
  [(((x B)) . ⊢ . t Bool)
   ---------------------- "BaseC"
   (⊢c {x : B t} B)]
  
  [(⊢c c_1 T_1)
   (⊢c c_2 T_2)
   ------------------------------ "FunC"
   (⊢c (c_1 ↦ c_2) (T_1 -> T_2))])

(define-metafunction λc
  ⊃ : t t -> #t or #f
  [(⊃ t_1 t_2)
   ,(if (eq? (term true) (term B_1))
        (eq? (term true) (term B_2))
        #t)
   (where ((B_1) (B_2))
          (,(apply-reduction-relation* ->λc (term t_1))
           ,(apply-reduction-relation* ->λc (term t_2))))])

;; ----------------------------------------------------------------------------

(module+ test
  (define t1 (term (({x : Int true} "l" "l'") 1)))
  (define r1 (term 1))
  (define T1 (term Int))
  
  (define t2 (term (({x : Int (nonzero x)} "l" "l'") 1)))
  (define r2 (term 1))
  (define T2 (term Int))
  
  (define t3 (term (({y : Int (pos y)} "l" "l'") 1)))
  (define r3 (term 1))
  (define T3 (term Int))
  
  (define t4 (term (({y : Int (pos y)} "l" "l'") -1)))
  (define r4 (term (⇑ "l")))
  (define T4 (term Int))
  
  (define t5 (term (((({x : Int (nonzero x)} ↦ {x : Int (pos x)}) "l" "l'")
                     (λ (x : Int) (pred x))) 0)))
  (define r5 (term (⇑ "l'")))
  (define T5 (term Int))
  
  (define t6 (term (((({x : Int (nonzero x)} ↦ {x : Int (pos x)}) "l" "l'")
                     (λ (x : Int) (pred x))) 1)))
  (define r6 (term (⇑ "l")))
  (define T6 (term Int))
  
  (define t7 (term (((({x : Int (nonzero x)} ↦ {x : Int (pos x)}) "l" "l'")
                     (λ (x : Int) (pred x))) 2)))
  (define r7 (term 1))
  (define T7 (term Int))
  
  (for ([t (list t1 t2 t3 t4 t5 t6 t7)]
        [r (list r1 r2 r3 r4 r5 r6 r7)]
        [T (list T1 T2 T3 T4 T5 T6 T7)])
    (test-->> ->λc t r)
    (test-equal (judgment-holds (() . ⊢ . ,t T) T) (term (,T)))))