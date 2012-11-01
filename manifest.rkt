#lang racket

(require redex "base.rkt")

(provide λh ->λh ⊢λh erase)

;; ----------------------------------------------------------------------------
;; Syntax for λh

(define-extended-language λh base
  [S .... {x : B s}]
  [s .... (S ⇒ S l)]
  [w .... (S ⇒ S l) (((S -> S) ⇒ (S -> S) l) w)])

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
   [--> (in-hole F s_1) (in-hole F s_2)
        (where (s_2) ,(apply-reduction-relation ->λh (term s_1)))
        "Compat"]))

;; ----------------------------------------------------------------------------
;; Typing rules for λh

(define-judgment-form λh
  #:mode (⊢λh I I I)
  #:contract (⊢λh ∆ s S)
  
  [(⊢swf S)
   -------------------- "Blame"
   (∆ . ⊢λh . (⇑ l) S)]
  
  [(∆ . ⊢ . s S_1)
   (⊢swf S_2)
   (S_1 . <: . S_2)
   ------------------ "Sub"
   (∆ . ⊢λh . s S_2)]
  
  [(∆ . ⊢ . s S)
   ---------------- "Compat"
   (∆ . ⊢λh . s S)])

(define-extended-judgment-form λh ⊢base
  #:mode (⊢ I I O)
  #:contract (⊢ ∆ s S)
  
  [(⊢swf S_1)
   (⊢swf S_2)
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
  
  [(() . ⊢ . k {x_1 : B true})
   (() . ⊢ . s_2 {x_2 : Bool true})
   (⊢swf {x : B s_1})
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
    (all (((subst x_1 k s_1) . ⊃ . (subst x_2 k s_2)) ...)))
   --------------------------------------------------------- "Refine"
   ({x_1 : B s_1} . <: . {x_2 : B s_2})]
  
  [(S_21 . <: . S_11)
   (S_12 . <: . S_22)
   --------------------------------------- "Fun"
   ((S_11 -> S_12) . <: . (S_21 -> S_22))])

(define-judgment-form λh
  #:mode (⊢swf I)
  #:contract (⊢swf S)
  
  [(⊢swf {x : B true}) "Raw"]
  
  [(((x {x : B true})) . ⊢ . s {x : Bool true})
   -------------------------------------------- "Refine"
   (⊢swf {x : B s})]
  
  [(⊢swf S_1)
   (⊢swf S_2)
   -------------------- "Fun"
   (⊢swf (S_1 -> S_2))])

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
  (define (test s r S)
    (test-->> ->λh s r)
    (test-equal (judgment-holds (() . ⊢λh . ,s ,S)) #t)
    (test-equal (judgment-holds (() . ⊢λh . ,r ,S)) #t))
  
  (define I (term {x : Int true}))
  (define N (term {x : Int (nonzero x)}))
  (define P (term {x : Int (pos x)}))
  (define N->I (term (,N -> ,I)))
  (define I->P (term (,I -> ,P)))
  (define pred (term (λ (x : ,I) (pred x))))
  
  (test (term ((,I ⇒ ,I "l") 1)) 1 I)
  (test (term ((,I ⇒ ,N "l") 1)) 1 N)
  (test (term ((,I ⇒ ,P "l") 1)) 1 P)
  (test (term ((,I ⇒ ,P "l") -1)) (term (⇑ "l")) P)
  (test (term (((,N->I ⇒ ,I->P "l") ,pred) 0)) (term (⇑ "l")) P)
  (test (term (((,N->I ⇒ ,I->P "l") ,pred) 1)) (term (⇑ "l")) P)
  (test (term (((,N->I ⇒ ,I->P "l") ,pred) 2)) 1 P))