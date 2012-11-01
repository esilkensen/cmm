#lang racket

(require redex "base.rkt" "latent.rkt")

(provide dep-λc ->lax-λc ->picky-λc)

;; ----------------------------------------------------------------------------
;; Syntax for dependent λc

(define-extended-language dep-λc λc
  [c .... (x : c ↦ c)]
  [d T (c l l)]
  [Γ ((x d) ...)])

;; ----------------------------------------------------------------------------
;; Operational semantics for dependent λc

(define ->lax-λc
  (extend-reduction-relation
   ->λc dep-λc
   [--> ((((x : c_1 ↦ c_2) l_p l_n) v_1) v_2)
        (((subst x v_2 c_2) l_p l_n) (v_1 ((c_1 l_n l_p) v_2)))
        "CDecompLax"]))

(define ->picky-λc
  (extend-reduction-relation
   ->λc dep-λc
   [--> ((((x : c_1 ↦ c_2) l_p l_n) v_1) v_2)
        (((subst x ((c_1 l_n l_p) v_2) c_2) l_p l_n) (v_1 ((c_1 l_n l_p) v_2)))
        "CDecompPicky"]))

;; ----------------------------------------------------------------------------

(module+ test  
  (define Pos (term {x : Int (pos x)}))
  (define (f n)
    (term (((g : (,Pos ↦ ,Pos) ↦ {z : Int (= z (g 0))}) "l_f" "l_g")
           (λ (g : (Int -> Int)) (g ,n)))))
  (define t1 (term (,(f 1) (λ (x : Int) 1))))
  (test-->> ->lax-λc t1 1)
  (test-->> ->picky-λc t1 (term (⇑ "l_f"))))