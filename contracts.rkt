#lang racket

(require redex)

;;----------------------------------------------------------------------------
;; Base types and constants for λc and λh

(define-language base
  (B Bool Int)
  (k true false number)
  (l string)
  (x variable-not-otherwise-mentioned))

;; ----------------------------------------------------------------------------
;; Syntax for λc

(define-extended-language λc base
  (T B (T -> T))
  (c {x : B t} (c ↦ c))
  (t x k (λ (x : T) t) (t t) (⇑ l) (c l l) ({x : B t} t k l))
  (v k (λ (x : T) t) (c l l) ((c ↦ c l l) v))
  (r v (⇑ l))
  (E (hole t) (v hole) ({x : B t} hole k l)))

;; ----------------------------------------------------------------------------
;; Operational semantics for λc

(define ->λc
  (reduction-relation
   λc
   [--> ((λ (x : T) t) v) (subst x v t) "E_Beta"]
   [--> ((((c_1 ↦ c_2) l_p l_n) v_1) v_2)
        ((c_2 l_p l_n) (v_1 ((c_1 l_n l_p) v_2)))
        "E_CDecomp"]
   [--> (({x : B t} l_p l_n) k)
        ({x : B t} (subst x k t) k l_p)
        "E_CCheck"]
   [--> ({x : B t} true k l) k "E_OK"]
   [--> ({x : B t} false k l) (⇑ l) "E_False"]
   [--> (in-hole E (⇑ l)) (⇑ l) "E_Blame"]
   [--> (in-hole E t_1) (in-hole E t_2)
        (where (t_2) ,(apply-reduction-relation ->λc (term t_1)))
        "E_Compat"]))

;; ----------------------------------------------------------------------------
;; Typing rules for λc

(define-extended-language λc+Γ λc
  [Γ ((x T) ...)])

(define-judgment-form λc+Γ
  #:mode (⊢ I I O)
  #:contract (⊢ Γ t T)
  
  [(where T (lookup x Γ))
   ---------------------- "T_Var"
   (Γ . ⊢ . x T)]
  
  [(where T (ty-c k))
   ------------------ "T_Const"
   (Γ . ⊢ . k T)]
  
  [((extend x T_1 Γ) . ⊢ . t T_2)
   --------------------------------------- "T_Lam"
   (Γ . ⊢ . (λ (x : T_1) t) (T_1 -> T_2))]
  
  [(Γ . ⊢ . t_1 (T_1 -> T_2))
   (Γ . ⊢ . t_2 T_1)
   -------------------------- "T_App"
   (Γ . ⊢ . (t_1 t_2) T_2)]
  
  [(⊢c c T)
   ------------------------------- "T_Contract"
   (Γ . ⊢ . (c l_p l_n) (T -> T))]
  
  [(() . ⊢ . k B)
   (() . ⊢ . t_2 Bool)
   (⊢c {x : B t_1} B)
   (side-condition
    (t_2 . ⊃ . (subst x k t_1)))
   ----------------------------------- "T_Checking"
   (() . ⊢ . ({x : B t_1} t_2 k l) B)])

(define-judgment-form λc+Γ
  #:mode (⊢c I O)
  #:contract (⊢c c T)
  
  [(((x B)) . ⊢ . t Bool)
   ---------------------- "T_BaseC"
   (⊢c {x : B t} B)]
  
  [(⊢c c_1 T_1)
   (⊢c c_2 T_2)
   ------------------------------ "T_FunC"
   (⊢c (c_1 ↦ c_2) (T_1 -> T_2))])

(define-metafunction λc+Γ
  ⊃ : t t -> #t or #f
  [(⊃ t_1 t_2)
   ,(if (eq? (term true) (term B_1))
        (eq? (term true) (term B_2))
        #t)
   (where ((B_1) (B_2))
          (,(apply-reduction-relation* ->λc (term t_1))
           ,(apply-reduction-relation* ->λc (term t_2))))])

(define-metafunction λc
  ty-c : k -> T
  [(ty-c true) Bool]
  [(ty-c false) Bool]
  [(ty-c number) Int])

(define-metafunction λc+Γ
  lookup : x Γ -> T or #f
  [(lookup x ()) #f]
  [(lookup x ((x T) (x_1 T_1) ...)) T]
  [(lookup x ((x_1 T_1) (x_2 T_2) ...))
   (lookup x ((x_2 T_2) ...))])

(define-metafunction λc+Γ
  extend : x T Γ -> Γ
  [(extend x T ((x_1 T_1) ...))
   ((x T) (x_1 T_1) ...)])

;; ----------------------------------------------------------------------------

(define-metafunction λc
  subst : x any any -> any
  [(subst x any_1 (λ (x : T) any_2))
   (λ (x : T) any_2)]
  [(subst x_1 any_1 (λ (x_2 : T) any_2))
   (λ (x_new : T)
     (subst x_1 any_1 (subst-vars (x_2 x_new) any_2)))
   (where x_new
          ,(variable-not-in
            (term (x_1 any_1 any_2)) 
            (term x_2)))]
  [(subst x_1 any_1 x_1) any_1]
  [(subst x_1 any_1 x_2) x_2]
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction λc
  subst-vars : (x any) ... any -> any
  [(subst-vars (x_1 any_1) x_1) any_1]
  [(subst-vars (x_1 any_1) (any_2 ...)) 
   ((subst-vars (x_1 any_1) any_2) ...)]
  [(subst-vars (x_1 any_1) any_2) any_2]
  [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3) 
   (subst-vars (x_1 any_1) 
               (subst-vars (x_2 any_2) ... any_3))]
  [(subst-vars any) any])

;; ----------------------------------------------------------------------------

(module+ test
  (define t1 (term (({x : Int true} "l" "l'") 1)))
  (test-->> ->λc t1 (term 1))
  (test-equal (judgment-holds (() . ⊢ . ,t1 T) T) (term (Int))))