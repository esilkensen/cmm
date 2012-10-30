#lang racket

(require redex "base.rkt")

;; ----------------------------------------------------------------------------
;; Syntax for λh

(define-extended-language λh base
  (S {x : B s} (S -> S))
  (s x k (λ (x : S) s) (s s) (⇑ l) (S ⇒ S l) ({x : B s} s k l) (O s ...))
  (w k (λ (x : S) s) (S ⇒ S l) (((S -> S) ⇒ (S -> S) l) w))
  (q w (⇑ l))
  (F (hole s) (w hole) ({x : B s} hole k l) (O hole s ...) (O w ... hole)))

;; ----------------------------------------------------------------------------
;; Operational semantics for λh

(define ->λh
  (reduction-relation
   λh
   [--> ((λ (x : S) s) w) (subst x w s) "F_Beta"]
   [--> ((((S_11 -> S_12) ⇒ (S_21 -> S_22) l) w_1) w_2)
        ((S_12 ⇒ S_22 l) (w_1 ((S_21 ⇒ S_11 l) w_2)))
        "F_CDecomp"]
   [--> (({x_1 : B s_1} ⇒ {x_2 : B s_2} l) k)
        ({x_2 : B s_2} (subst x_2 k s_2) k l)
        "F_CCheck"]
   [--> ({x : B s} true k l) k "F_OK"]
   [--> ({x : B s} false k l) (⇑ l) "F_Fail"]
   [--> (in-hole F (⇑ l)) (⇑ l) "F_Blame"]
   [--> (in-hole F s_1) (in-hole F s_2)
        (where (s_2) ,(apply-reduction-relation ->λh (term s_1)))
        "F_Compat"]
   [--> (O w ...) (δ O w ...) "F_Prim"]))

;; ----------------------------------------------------------------------------
;; Typing rules for λh

(define-extended-language λh+∆ λh
  [∆ ((x S) ...)])

(define-judgment-form λh+∆
  #:mode (⊢ I I O)
  #:contract (⊢ ∆ s S)
  
  [(where S (lookup x ∆))
   ---------------------- "S_Var"
   (∆ . ⊢ . x S)]
  
  [(where S (ty-h k))
   ------------------ "S_Const"
   (∆ . ⊢ . k S)]
  
  [((extend x S_1 ∆) . ⊢ . s S_2)
   --------------------------------------- "S_Lam"
   (∆ . ⊢ . (λ (x : S_1) s) (S_1 -> S_2))]
  
  [(∆ . ⊢ . s_1 (S_1 -> S_2))
   (∆ . ⊢ . s_2 S_1)
   -------------------------- "S_App"
   (∆ . ⊢ . (s_1 s_2) S_2)]
  
  [(⊢c S_1)
   (⊢c S_2)
   (side-condition
    (equal (erase S_1) (erase S_2)))
   ------------------------------------- "S_Cast"
   (∆ . ⊢ . (S_1 ⇒ S_2 l) (S_1 -> S_2))]
  
;  [(⊢c S)
;   ------------------ "S_Blame"
;   (∆ . ⊢ . (⇑ l) S)]
  
;  [(∆ . ⊢ . s S_1)
;   (⊢c S_2)
;   (S_1 . <: . S_2)
;   ---------------- "S_Sub"
;   (∆ . ⊢ . s S_2)]
  
  [(() . ⊢ . k {x_1 : B true})
   (() . ⊢ . s_2 {x_2 : Bool true})
   (⊢c {x : B s_1})
   (side-condition
    (s_2 . ⊃ . (subst x k s_1)))
   --------------------------------------------- "S_Checking"
   (() . ⊢ . ({x : B s_1} s_2 k l) {x : B s_1})]
  
  [(∆ . ⊢ . s Int)
   ----------------------- "S_Pos"
   (∆ . ⊢ . (pos s) Bool)]
  
  [(∆ . ⊢ . s Int)
   --------------------------- "S_Nonzero"
   (∆ . ⊢ . (nonzero s) Bool)]
  
  [(∆ . ⊢ . s_1 B)
   (∆ . ⊢ . s_2 B)
   --------------------------- "S_Equal"
   (∆ . ⊢ . (= s_1 s_2) Bool)]
  
  [(∆ . ⊢ . s Int)
   ----------------------- "S_Pred"
   (∆ . ⊢ . (pred s) Int)])

(define-judgment-form λh+∆
  #:mode (<: I I)
  #:contract (<: S S)
  
  [(where (k ...) (K B))
   (side-condition
    (((subst x_1 k s_1) . ⊃ . (subst x_2 k s_2)) ...))
   --------------------------------------------------- "SSub_Refine"
   ({x_1 : B s_1} . <: . {x_2 : B s_2})]
  
  [(S_21 . <: . S_11)
   (S_12 . <: . S_22)
   --------------------------------------- "SSub_Fun"
   ((S_11 -> S_12) . <: . (S_21 -> S_22))])

(define-judgment-form λh+∆
  #:mode (⊢c I)
  #:contract (⊢c S)
  
  [(⊢c {x : B true}) "SWF_Raw"]
  
  [(((x {x : B true})) . ⊢ . s {x : Bool true})
   -------------------------------------------- "SWF_Refine"
   (⊢c {x : B s})]
  
  [(⊢c S_1)
   (⊢c S_2)
   ------------------ "SWF_Fun"
   (⊢c (S_1 -> S_2))])

(define-metafunction λh+∆
  ⊃ : s s -> #t or #f
  [(⊃ s_1 s_2)
   ,(if (eq? (term true) (term B_1))
        (eq? (term true) (term B_2))
        #t)
   (where ((B_1) (B_2))
          (,(apply-reduction-relation* ->λh (term s_1))
           ,(apply-reduction-relation* ->λh (term s_2))))])

(define-metafunction λh
  K : B -> (k ...)
  [(K Bool) (true false)]
  [(K Int) (-1 0 1)])

(define-metafunction λh
  ty-h : k -> S
  [(ty-h k) {x : B (= x k)}])

(define-metafunction λh+∆
  lookup : x ∆ -> S or #f
  [(lookup x ()) #f]
  [(lookup x ((x S) (x_1 S_1) ...)) S]
  [(lookup x ((x_1 S_1) (x_2 S_2) ...))
   (lookup x ((x_2 S_2) ...))])

(define-metafunction λh+∆
  extend : x S ∆ -> ∆
  [(extend x S ((x_1 S_1) ...))
   ((x S) (x_1 S_1) ...)])

;; ----------------------------------------------------------------------------

(define-metafunction λh
  subst : x any any -> any
  [(subst x any_1 (λ (x : S) any_2))
   (λ (x : S) any_2)]
  [(subst x_1 any_1 (λ (x_2 : S) any_2))
   (λ (x_new : S)
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

(define-metafunction λh
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
  (define s1 (term (({x : Int true} ⇒ {x : Int true} "l") 1)))
  (define q1 (term 1))
  
  (define s2 (term (({x : Int true} ⇒ {x : Int (nonzero x)} "l") 1)))
  (define q2 (term 1))
  
  (define s3 (term (({x : Int true} ⇒ {y : Int (pos y)} "l") 1)))
  (define q3 (term 1))
  
  (define s4 (term (({x : Int true} ⇒ {y : Int (pos y)} "l") -1)))
  (define q4 (term (⇑ "l")))
  
  (define s5 (term (((({x : Int (nonzero x)} -> {x : Int true})
                      ⇒ ({x : Int true} -> {y : Int (pos y)}) "l")
                     (λ (x : {x : Int true}) (pred x))) 0)))
  (define q5 (term (⇑ "l")))
  
  (define s6 (term (((({x : Int (nonzero x)} -> {x : Int true})
                      ⇒ ({x : Int true} -> {y : Int (pos y)}) "l")
                     (λ (x : {x : Int true}) (pred x))) 1)))
  (define q6 (term (⇑ "l")))
  
  (define s7 (term (((({x : Int (nonzero x)} -> {x : Int true})
                      ⇒ ({x : Int true} -> {y : Int (pos y)}) "l")
                     (λ (x : {x : Int true}) (pred x))) 2)))
  (define q7 (term 1))
  
  (for ([s (list s1 s2 s3 s4 s5 s6 s7)]
        [q (list q1 q2 q3 q4 q5 q6 q7)])
    (test-->> ->λh s q)))