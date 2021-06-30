#lang racket
(require redex)

;; Cylindrical logic

(define-language cyl
  (τ (τ → τ) (τ × τ) (c κ τ) (d κ κ) Z)
  (e x
     integer

     (e e)
     (λ (x τ) e)

     (box κ e)
     (cons e e)
     (head e)
     (tail e)

     (refl κ)
     (sym e)
     (e ∘ e)
     )
  (κ integer)
  (x variable-not-otherwise-mentioned)
 
  #:binding-forms
  (λ (x τ) e #:refers-to x))

(define-extended-language cyl+Γ cyl
  [Γ () (p ...)]
  [p [x : τ]])

(define-judgment-form cyl+Γ
  #:mode (types I I O)
  #:contract (types Γ e τ)
 
 
  [-------------------------
   (types Γ integer Z)]

   [(types Γ e_0 (τ_0 → τ_1)) (types Γ e_1 τ_0)
   -------------------------
   (types Γ (e_0 e_1) τ_1)]

  [(types ([x : τ_0] p ...) e τ_1)
   -------------------------
   (types (p ...) (λ (x τ_0) e) (τ_0 → τ_1))]


  [ (types Γ e τ)
    -------------------------
   (types Γ (box κ e) (c κ τ))]
   [(types Γ e_0 (c κ τ_0))
    (types Γ e_1 (c κ τ_1))
    -------------------------
    (types Γ (cons e_0 e_1) (c κ (τ_0 × (c κ τ_1))))]
  [ (types Γ e (c κ (τ_0 × (c κ τ_1))))
    -------------------------
   (types Γ (head e) (c κ τ_0))]
  [ (types Γ e (c κ (τ_0 × (c κ τ_1))))
    -------------------------
   (types Γ (tail e) (c κ τ_1))]

  [
   -------------------------
   (types Γ (refl κ) (d κ κ))]
  [(types Γ e (d κ_0 κ_1))
   -------------------------
   (types Γ (sym e) (d κ_1 κ_0))]
  [(types Γ e_0 (d κ_1 κ_2)) (types Γ e_1 (d κ_0 κ_1))
    -------------------------
   (types Γ (e_0 ∘ e_1) (d κ_0 κ_2))]
  )

(define-extended-language cyl+stk cyl
  (E hole
     (E e)))

(define cyl-whnf
  (reduction-relation cyl+stk #:domain e
   (--> (in-hole E ((λ (x τ) e_0) e_1))
        (in-hole E (substitute e_1 x e_0))
        "λ-subst")

   (--> (in-hole E (head (cons e_0 e_1)))
        (in-hole E e_0)
        "c-head")
   (--> (in-hole E (tail (cons e_0 e_1)))
        (in-hole E e_1)
        "c-tail")

   (--> (in-hole E ((refl κ) ∘ (refl κ)))
        (in-hole E (refl κ))
        "d-compose")
   (--> (in-hole E (sym (refl κ)))
        (in-hole E (refl κ))
        "d-sym")
        )
       )

(render-language cyl)
(render-judgment-form types)
(render-reduction-relation cyl-whnf)

(judgment-holds
   (types () 4 τ)
   τ)
(traces cyl-whnf (term ((λ (x Z) x) 4)))
(traces cyl-whnf (term (tail (cons (box 0 4) (box 0 8))))) 
(test-->
 cyl-whnf
 (term ((λ (x Z) x) 4)) (term 4))
