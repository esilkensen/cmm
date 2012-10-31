#lang racket

(require redex)

(provide base ->base ⊢base δ ty lookup extend equal all subst)

;;----------------------------------------------------------------------------
;; Base types and constants and common syntax for λc and λh

(define-language base
  [B Bool Int]
  [(T S) (T -> T)]
  [(t s) x k (λ (x : T) t) (t t) (⇑ l) ({x : B t} t k l) (O t ...)]
  [(v w) k (λ (x : T) t)]
  [(r q) v (⇑ l) error]
  [(E F) (hole t) (v hole) ({x : B t} hole k l) (O hole t ...) (O v ... hole)]
  [(Γ ∆) ((x T) ...)]
  [O pos nonzero = pred]
  [l string]
  [k true false number]
  [x variable-not-otherwise-mentioned])

;; ----------------------------------------------------------------------------
;; Common reduction rules for λc and λh

(define ->base
  (reduction-relation
   base
   [--> ((λ (x : T) t) v) (subst x v t) "Beta"]
   [--> ({x : B t} true k l) k "OK"]
   [--> ({x : B t} false k l) (⇑ l) "Fail"]
   [--> (in-hole E (⇑ l)) (⇑ l) "Blame"]
   [--> (O v ...) (δ O v ...) "Prim"]))

(define-metafunction base
  δ : O k ... -> k
  [(δ pos k)
   ,(if (positive? (term k))
        (term true)
        (term false))]
  [(δ nonzero k)
   ,(if (not (zero? (term k)))
        (term true)
        (term false))]
  [(δ = k_1 k_2)
   ,(if (eq? (term k_1) (term k_2))
        (term true)
        (term false))]
  [(δ pred k) ,(- (term k) 1)])

;; ----------------------------------------------------------------------------
;; Common typing rules for λc and λh

(define-judgment-form base
  #:mode (⊢base I I O)
  #:contract (⊢base Γ t T)
  
  [(where T (lookup x Γ))
   ---------------------- "Var"
   (Γ . ⊢base . x T)]
  
  [(where T (ty k))
   ---------------- "Const"
   (Γ . ⊢base . k T)]
  
  [((extend x T_1 Γ) . ⊢base . t T_2)
   --------------------------------------- "Lam"
   (Γ . ⊢base . (λ (x : T_1) t) (T_1 -> T_2))]
  
  [(Γ . ⊢base . t_1 (T_1 -> T_2))
   (Γ . ⊢base . t_2 T_1)
   -------------------------- "App"
   (Γ . ⊢base . (t_1 t_2) T_2)])

(define-metafunction base
  ty : k -> B
  [(ty true) Bool]
  [(ty false) Bool]
  [(ty number) Int])

(define-metafunction base
  lookup : x ((x any) ...) -> any or #f
  [(lookup x ()) #f]
  [(lookup x ((x any) (x_1 any_1) ...)) any]
  [(lookup x ((x_1 any_1) (x_2 any_2) ...))
   (lookup x ((x_2 any_2) ...))])

(define-metafunction base
  extend : x any ((x any) ...) -> ((x any) ...)
  [(extend x any ((x_1 any_1) ...))
   ((x any) (x_1 any_1) ...)])

;;----------------------------------------------------------------------------

(define-metafunction base
  [(equal any any) #t]
  [(equal any_1 any_2) #f])

(define-metafunction base
  all : (any ...) -> #t or #f
  [(all ()) #t]
  [(all (#f any ...)) #f]
  [(all (#t any ...)) (all (any ...))])

(define-metafunction base
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

(define-metafunction base
  [(subst-vars (x_1 any_1) x_1) any_1]
  [(subst-vars (x_1 any_1) (any_2 ...)) 
   ((subst-vars (x_1 any_1) any_2) ...)]
  [(subst-vars (x_1 any_1) any_2) any_2]
  [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3) 
   (subst-vars (x_1 any_1) 
               (subst-vars (x_2 any_2) ... any_3))]
  [(subst-vars any) any])