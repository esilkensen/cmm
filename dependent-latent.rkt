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
        "CDecompLax"]
   [--> (in-hole E t_1) (in-hole E t_2)
        (where (t_2) ,(apply-reduction-relation ->lax-λc (term t_1)))
        "Compat"]))

(define ->picky-λc
  (extend-reduction-relation
   ->λc dep-λc
   [--> ((((x : c_1 ↦ c_2) l_p l_n) v_1) v_2)
        (((subst x ((c_1 l_n l_p) v_2) c_2) l_p l_n) (v_1 ((c_1 l_n l_p) v_2)))
        "CDecompPicky"]
   [--> (in-hole E t_1) (in-hole E t_2)
        (where (t_2) ,(apply-reduction-relation ->picky-λc (term t_1)))
        "Compat"]))

;; ----------------------------------------------------------------------------

(module+ test  
  (define Pos (term {x : Int (pos x)}))
  (define (f n)
    (term (((g : (,Pos ↦ ,Pos) ↦ {z : Int (= z (g 0))}) "l_f" "l_g")
           (λ (g : (Int -> Int)) (g ,n)))))
  (define t1 (term (,(f 1) (λ (x : Int) 1))))
  (test-->> ->lax-λc t1 1)
  (test-->> ->picky-λc t1 (term (⇑ "l_f")))
  
  (define I (term {x : Int true}))
  (define N (term {x : Int (nonzero x)}))
  (define t2 (term ((((f : (,N ↦ ,I) ↦ {z : Int (= (f 0) 0)}) "l_f" "l_g")
                     (λ (f : (Int -> Int)) (f 5)))
                    (λ (x : Int) x))))
  (test-->> ->lax-λc t2 5)
  (test-->> ->picky-λc t2 (term (⇑ "l_f"))))