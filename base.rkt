#lang racket

(require redex)

(provide base δ)

;;----------------------------------------------------------------------------
;; Base types and constants for λc and λh

(define-language base
  (B Bool Int)
  (k true false number)
  (O pos nonzero = pred)
  (l string)
  (x variable-not-otherwise-mentioned))

;; ----------------------------------------------------------------------------
;; Utility metafunctions for λc and λh

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
