#lang racket

(require redex "base.rkt")

(provide λc ->λc ⊢λc)

;; ----------------------------------------------------------------------------
;; Syntax for λc

(define-extended-language λc base
  [T .... B]
  [t .... (c l l)]
  [v .... (c l l) ((c ↦ c l l) v)]
  [c {x : B t} (c ↦ c)])

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

(define-judgment-form λc
  #:mode (⊢λc I I I)
  #:contract (⊢λc Γ t T)
  
  [(Γ . ⊢λc . (⇑ l) T) "Blame"]
  
  [(Γ . ⊢ . t T)
   ---------------- "Compat"
   (Γ . ⊢λc . t T)])

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
   (() . ⊢ . ({x : B t_1} t_2 k l) B)]
  
  [(Γ . ⊢ . t Int)
   ----------------------- "Pos"
   (Γ . ⊢ . (pos t) Bool)]
  
  [(Γ . ⊢ . t Int)
   --------------------------- "Nonzero"
   (Γ . ⊢ . (nonzero t) Bool)]
  
  [(Γ . ⊢ . t_1 B)
   (Γ . ⊢ . t_2 B)
   --------------------------- "Equal"
   (Γ . ⊢ . (= t_1 t_2) Bool)]
  
  [(Γ . ⊢ . t Int)
   ----------------------- "Pred"
   (Γ . ⊢ . (pred t) Int)])

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
   ,(if (eq? (term true) (term v_1))
        (eq? (term true) (term v_2))
        #t)
   (where ((v_1) (v_2))
          (,(apply-reduction-relation* ->λc (term t_1))
           ,(apply-reduction-relation* ->λc (term t_2))))])

;; ----------------------------------------------------------------------------

(module+ test
  (define (test t r T)
    (test-->> ->λc t r)
    (test-equal (judgment-holds (() . ⊢λc . ,t ,T)) #t)
    (test-equal (judgment-holds (() . ⊢λc . ,r ,T)) #t))
  
  (define I (term {x : Int true}))
  (define N (term {x : Int (nonzero x)}))
  (define P (term {x : Int (pos x)}))
  (define pred (term (λ (x : Int) (pred x))))
  
  (test (term ((,I "l" "l'") 1)) 1 (term Int))
  (test (term ((,N "l" "l'") 1)) 1 (term Int))
  (test (term ((,P "l" "l'") 1)) 1 (term Int))
  (test (term ((,P "l" "l'") -1)) (term (⇑ "l")) (term Int))
  (test (term ((((,N ↦ ,P) "l" "l'") ,pred) 0)) (term (⇑ "l'")) (term Int))
  (test (term ((((,N ↦ ,P) "l" "l'") ,pred) 1)) (term (⇑ "l")) (term Int))
  (test (term ((((,N ↦ ,P) "l" "l'") ,pred) 2)) 1 (term Int)))