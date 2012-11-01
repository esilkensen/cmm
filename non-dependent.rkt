#lang racket

(require redex "base.rkt" "latent.rkt" "manifest.rkt")

(provide ψ φ)

;; ----------------------------------------------------------------------------
;; Translating from λh to λc

(define-metafunction λh
  [(ψ {x_1 : B s_1} {x_2 : B s_2}) {x_2 : B (ψ s_2)}]
  [(ψ (S_11 -> S_12) (S_21 -> S_22)) ((ψ S_21 S_11) ↦ (ψ S_12 S_22))]
  [(ψ (S_1 ⇒ S_2 l)) ((ψ S_1 S_2) l l)]
  [(ψ x) x]
  [(ψ k) k]
  [(ψ (λ (x : S) s)) (λ (x : (erase S)) (ψ s))]
  [(ψ (s_1 s_2)) ((ψ s_1) (ψ s_2))]
  [(ψ (⇑ l)) (⇑ l)]
  [(ψ ({x : B s_1} s_2 k l)) ({x : B (ψ s_1)} (ψ s_2) k l)]
  [(ψ (O s ...)) (O (ψ s) ...)])

;; ----------------------------------------------------------------------------
;; Translating from λc to λh

(define-metafunction λc
  [(φ (c l_p l_n)) 
   (λ (x : (raw c)) (((φ c) ⇒ (raw c) l_n) (((raw c) ⇒ (φ c) l_p) x)))]
  [(φ {x : B t}) {x : B (φ t)}]
  [(φ (c_1 ↦ c_2)) ((φ c_1) -> (φ c_2))]
  [(φ x) x]
  [(φ k) k]
  [(φ (λ (x : T) t)) (λ (x : (raw T)) (φ t))]
  [(φ (t_1 t_2)) ((φ t_1) (φ t_2))]
  [(φ (⇑ l)) (⇑ l)]
  [(φ ({x : B t_1} t_2 k l)) ({x : B (φ t_1)} (φ t_2) k l)]
  [(φ (O t ...)) (O (φ t) ...)])

(module+ test
  (define (test-ψ)
    (define (test s r)
      (test-->> ->λh s r)
      (test-->> ->λc (term (ψ ,s)) r))
    
    (define I (term {x : Int true}))
    (define N (term {x : Int (nonzero x)}))
    (define P (term {x : Int (pos x)}))
    (define N->I (term (,N -> ,I)))
    (define I->P (term (,I -> ,P)))
    (define pred (term (λ (x : ,I) (pred x))))
    
    (test (term ((,I ⇒ ,I "l") 1)) 1)
    (test (term ((,I ⇒ ,N "l") 1)) 1)
    (test (term ((,I ⇒ ,P "l") 1)) 1)
    (test (term ((,I ⇒ ,P "l") -1)) (term (⇑ "l")))
    (test (term (((,N->I ⇒ ,I->P "l") ,pred) 0)) (term (⇑ "l")))
    (test (term (((,N->I ⇒ ,I->P "l") ,pred) 1)) (term (⇑ "l")))
    (test (term (((,N->I ⇒ ,I->P "l") ,pred) 2)) 1))
  
  (define (test-φ)
    (define (test t r)
      (test-->> ->λc t r)
      (test-->> ->λh (term (φ ,t)) r))
    
    (define I (term {x : Int true}))
    (define N (term {x : Int (nonzero x)}))
    (define P (term {x : Int (pos x)}))
    (define pred (term (λ (x : Int) (pred x))))
    
    (test (term ((,I "l" "l'") 1)) 1)
    (test (term ((,N "l" "l'") 1)) 1)
    (test (term ((,P "l" "l'") 1)) 1)
    (test (term ((,P "l" "l'") -1)) (term (⇑ "l")))
    (test (term ((((,N ↦ ,P) "l" "l'") ,pred) 0)) (term (⇑ "l'")))
    (test (term ((((,N ↦ ,P) "l" "l'") ,pred) 1)) (term (⇑ "l")))
    (test (term ((((,N ↦ ,P) "l" "l'") ,pred) 2)) 1))
  
  (test-ψ)
  (test-φ))