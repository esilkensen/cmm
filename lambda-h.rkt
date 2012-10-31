#lang racket

(require redex "base.rkt")

;; ----------------------------------------------------------------------------
;; Syntax for λh

(define-extended-language λh base
  (S .... {x : B s})
  (s .... (S ⇒ S l))
  (w .... (S ⇒ S l) (((S -> S) ⇒ (S -> S) l) w)))

;; ----------------------------------------------------------------------------
;; Operational semantics for λh

(define ->λh
  (extend-reduction-relation
   ->base λh
   [--> ((((S_11 -> S_12) ⇒ (S_21 -> S_22) l) w_1) w_2)
        ((S_12 ⇒ S_22 l) (w_1 ((S_21 ⇒ S_11 l) w_2)))
        "CDecomp"]
   [--> (({x_1 : B s_1} ⇒ {x_2 : B s_2} l) k)
        ({x_2 : B s_2} (subst x_2 k s_2) k l)
        "CCheck"]
   [--> ({x : B t} false k l) (⇑ l (ty-h k)) "Fail"]
   [--> (in-hole F s_1) (in-hole F s_2)
        (where (s_2) ,(apply-reduction-relation ->λh (term s_1)))
        "Compat"]))

;; ----------------------------------------------------------------------------
;; Typing rules for λh

(define-extended-judgment-form λh ⊢base
  #:mode (⊢ I I O)
  #:contract (⊢ ∆ s S)
  
  [(⊢c S_1)
   (⊢c S_2)
   (side-condition
    (equal (erase S_1) (erase S_2)))
   ------------------------------------- "Cast"
   (∆ . ⊢ . (S_1 ⇒ S_2 l) (S_1 -> S_2))]
  
  [(where T (ty-h k))
   ------------------ "Const"
   (Γ . ⊢ . k T)]
  
  [(Γ . ⊢ . t_1 (T_1 -> T_2))
   (Γ . ⊢ . t_2 T_0)
   (T_0 . <: . T_1)
   ------------------------ "App"
   (Γ . ⊢ . (t_1 t_2) T_2)]
  
  [(⊢c S)
   -------------------- "Blame"
   (∆ . ⊢ . (⇑ l S) S)]
  
  [(() . ⊢ . k {x_1 : B true})
   (() . ⊢ . s_2 {x_2 : Bool true})
   (⊢c {x : B s_1})
   (side-condition
    (s_2 . ⊃ . (subst x k s_1)))
   --------------------------------------------- "Checking"
   (() . ⊢ . ({x : B s_1} s_2 k l) {x : B s_1})]
  
  [(∆ . ⊢ . s {x : Int true})
   ---------------------------------- "Pos"
   (∆ . ⊢ . (pos s) {x : Bool true})]
  
  [(∆ . ⊢ . s {x : Int true})
   -------------------------------------- "Nonzero"
   (∆ . ⊢ . (nonzero s) {x : Bool true})]
  
  [(∆ . ⊢ . s_1 {x_1 : B true})
   (∆ . ⊢ . s_2 {x_2 : B true})
   ---------------------------------------- "Equal"
   (∆ . ⊢ . (= s_1 s_2) {x_1 : Bool true})]
  
  [(∆ . ⊢ . s {x : Int true})
   ---------------------------------- "Pred"
   (∆ . ⊢ . (pred s) {x : Int true})])

(define-judgment-form λh
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

(define-judgment-form λh
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

(define-metafunction λh
  ⊃ : s s -> #t or #f
  [(⊃ s_1 s_2)
   ,(if (eq? (term true) (term v_1))
        (eq? (term true) (term v_2))
        #t)
   (where ((v_1) (v_2))
          (,(apply-reduction-relation* ->λh (term s_1))
           ,(apply-reduction-relation* ->λh (term s_2))))])

(define-metafunction λh
  K : B -> (k ...)
  [(K Bool) (true false)]
  [(K Int) (-1 0 1)])

(define-metafunction λh
  ty-h : k -> S
  [(ty-h k) {x : (ty k) (= x k)}])

(define-metafunction λh
  erase : S -> any
  [(erase {x : B s}) B]
  [(erase (S_1 -> S_2)) ((erase S_1) -> (erase S_2))])

;; ----------------------------------------------------------------------------

(module+ test
  (define s1 (term (({x : Int true} ⇒ {x : Int true} "l") 1)))
  (define q1 (term 1))
  (test-->> ->λh s1 q1)
  (test-equal
   (judgment-holds (() . ⊢ . ,s1 {x : Int true})) #t)
  (test-equal
   (judgment-holds (() . ⊢ . ,q1 {x : Int (= x 1)})) #t)
  (test-equal
   (judgment-holds ({x : Int (= x 1)} . <: . {x : Int true})) #t)
  
  (define s2 (term (({x : Int true} ⇒ {x : Int (nonzero x)} "l") 1)))
  (define q2 (term 1))
  (define S2 (term {x : Int (nonzero x)}))
  (test-->> ->λh s2 q2)
  (test-equal
   (judgment-holds (() . ⊢ . ,s2 {x : Int (nonzero x)})) #t)
  (test-equal
   (judgment-holds (() . ⊢ . ,q2 {x : Int (= x 1)})) #t)
  (test-equal
   (judgment-holds ({x : Int (= x 1)} . <: . {x : Int (nonzero x)})) #t)
  
  (define s3 (term (({x : Int true} ⇒ {x : Int (pos x)} "l") 1)))
  (define q3 (term 1))
  (test-->> ->λh s3 q3)
  (test-equal
   (judgment-holds (() . ⊢ . ,s3 {x : Int (pos x)})) #t)
  (test-equal
   (judgment-holds (() . ⊢ . ,q3 {x : Int (= x 1)})) #t)
  (test-equal
   (judgment-holds ({x : Int (= x 1)} . <: . {x : Int (pos x)})) #t)
  
  (define s4 (term (({x : Int true} ⇒ {y : Int (pos y)} "l") -1)))
  (define q4 (term (⇑ "l" {x : Int (= x -1)})))
  (test-->> ->λh s4 q4)
  (test-equal
   (judgment-holds (() . ⊢ . ,s4 {y : Int (pos y)})) #t)
  (test-equal
   (judgment-holds (() . ⊢ . ,q4 {x : Int (= x -1)})) #t)
  (test-equal
   (judgment-holds ({x : Int (= x -1)} . <: . {y : Int (pos y)})) #t)
  
  (define s5 (term (((({x : Int (nonzero x)} -> {x : Int true})
                      ⇒ ({x : Int true} -> {y : Int (pos y)}) "l")
                     (λ (x : {x : Int true}) (pred x))) 0)))
  (define q5 (term (⇑ "l" {x : Int (= x 0)})))
  (test-->> ->λh s5 q5)
  
  (define s6 (term (((({x : Int (nonzero x)} -> {x : Int true})
                      ⇒ ({x : Int true} -> {y : Int (pos y)}) "l")
                     (λ (x : {x : Int true}) (pred x))) 1)))
  (define q6 (term (⇑ "l" {x : Int (= x 0)})))
  (test-->> ->λh s5 q6)
  
  (define s7 (term (((({x : Int (nonzero x)} -> {x : Int true})
                      ⇒ ({x : Int true} -> {y : Int (pos y)}) "l")
                     (λ (x : {x : Int true}) (pred x))) 2)))
  (define q7 (term 1))
  (test-->> ->λh s7 q7))