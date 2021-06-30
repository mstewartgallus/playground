#lang racket
(require redex)

; Simple calculus loosely based around Tarski's cylindrical logic

(define-language cyl
  (z integer)
  (κ natural)

  (τ (τ → τ) (τ + τ) (τ × τ) (Σ κ τ) (κ = κ) Z)
  
  (v x
     (λ (x τ) e)
     (inl τ e)
     (inr τ e)
     (box κ e)
     (cons e e)
     (id κ)
     z)

  (e v
     (e e)
     (case e (x e) (x e))

     (cons e e)
     (head e)
     (tail e)

     (e ∘ e)
     (sym e)
     (cast e e)

     (e * e)
     (e + e)
     )

  (x variable-not-otherwise-mentioned)
 
  #:binding-forms
  (λ (x τ) e #:refers-to x)
  (case e (x e #:refers-to x) (x e #:refers-to x)))

(define-extended-language cyl+Γ cyl
  [Γ () (p ...)]
  [p [x : τ]])

(define-judgment-form cyl+Γ
  #:mode (types I I O)
  #:contract (types Γ e τ)
 
  ; Simply typed lambda calculus
  [(types Γ e_0 (τ_0 → τ_1)) (types Γ e_1 τ_0)
   -------------------------
   (types Γ (e_0 e_1) τ_1)]
  [(types ([x : τ_0] p ...) e τ_1)
   -------------------------
   (types (p ...) (λ (x τ_0) e) (τ_0 → τ_1))]

  ; Sum types
  [(types Γ e τ_0)
   -------------------------
   (types Γ (inl τ_1 e) (τ_0 + τ_1))]  
  [(types Γ e τ_1)
   -------------------------
   (types Γ (inr τ_0 e) (τ_0 + τ_1))]
  [(types (p ...) e_0 (τ_0 + τ_1))
   (types ([x_0 : τ_0] p ...) e_1 τ_2)
   (types ([x_1 : τ_1] p ...) e_2 τ_2)
   -------------------------
   (types (p ...) (case e_0 (x_0 e_1) (x_1 e_2)) τ_2)]

  ; Existential introduction/tuple manipulation
  [ (types Γ e τ)
    -------------------------
   (types Γ (box κ e) (Σ κ τ))]
   [(types Γ e_0 (Σ κ τ_0))
    (types Γ e_1 (Σ κ τ_1))
    -------------------------
    (types Γ (cons e_0 e_1) (Σ κ (τ_0 × (Σ κ τ_1))))]
  [ (types Γ e (Σ κ (τ_0 × (Σ κ τ_1))))
    -------------------------
   (types Γ (head e) (Σ κ τ_0))]
  [ (types Γ e (Σ κ (τ_0 × (Σ κ τ_1))))
    -------------------------
   (types Γ (tail e) (Σ κ τ_1))]

  ; Identity type reflexivity, transitivity and symmetry.
  [
   -------------------------
   (types Γ (id κ) (κ = κ))]
  [(types Γ e_0 (κ_1 = κ_2)) (types Γ e_1 (κ_0 = κ_1))
    -------------------------
   (types Γ (e_0 ∘ e_1) (κ_0 = κ_2))]
  [(types Γ e (κ_0 = κ_1))
   -------------------------
   (types Γ (sym e) (κ_1 = κ_0))]
  ; Use identity to cast from one sum to another
  ; Not at all sure of this rule
  [(types Γ e_0 (κ_0 = κ_1)) (types Γ e_1 (Σ κ_0 τ))  
   -------------------------
   (types Γ (cast e_0 e_1) (Σ κ_1 τ))]

  ; Some basic integer extras
  [-------------------------
   (types Γ integer Z)]
  [(types Γ e_0 Z) (types Γ e_1 Z)  
   -------------------------
   (types Γ (e_0 + e_1) Z)]
  [(types Γ e_0 Z) (types Γ e_1 Z)  
   -------------------------
   (types Γ (e_0 - e_1) Z)]
  [(types Γ e_0 Z) (types Γ e_1 Z)  
   -------------------------
   (types Γ (e_0 * e_1) Z)]
)

(define-extended-language cyl+stk cyl
  (E hole
     (E e)
     (case E (x e) (x e))

     (v ∘ E) (E ∘ e)
     (sym E)
     (cast E e) (cast v E)

     (E + e) (v + E)
     (E - e) (v - E)
     (E * e) (v * E)
    )
  
  #:binding-forms
  (case E (x e #:refers-to x) (x e #:refers-to x)))

(define-metafunction cyl+stk
  add : integer integer -> integer
  [(add integer_1 integer_2) ,(+ (term integer_1) (term integer_2))])
(define-metafunction cyl+stk
  sub : integer integer -> integer
  [(sub integer_1 integer_2) ,(- (term integer_1) (term integer_2))])
(define-metafunction cyl+stk
  mul : integer integer -> integer
  [(mul integer_1 integer_2) ,(* (term integer_1) (term integer_2))])

(define cyl-whnf
  (reduction-relation cyl+stk #:domain e
   (--> (in-hole E ((λ (x τ) e_0) e_1))
        (in-hole E (substitute e_1 x e_0))
        "λ-subst")

   (--> (in-hole E (case (inl τ e_0) (x_0 e_1) (x_1 e_2)))
        (in-hole E (substitute e_1 x_0 e_0))
        "+-case-inl")
   (--> (in-hole E (case (inr τ e_0) (x_0 e_1) (x_1 e_2)))
        (in-hole E (substitute e_2 x_1 e_0))
        "+-case-inr")
     
   (--> (in-hole E (head (cons e_0 e_1)))
        (in-hole E e_0)
        "Σ-head")
   (--> (in-hole E (tail (cons e_0 e_1)))
        (in-hole E e_1)
        "Σ-tail")

   (--> (in-hole E ((id κ) ∘ (id κ)))
        (in-hole E (id κ))
        "=-compose")
   (--> (in-hole E (sym (id κ)))
        (in-hole E (id κ))
        "=-sym")
   (--> (in-hole E (cast (id κ) (box κ e)))
        (in-hole E (box κ e))
        "=-cast")

   (--> (in-hole E (z_0 + z_1))
        (in-hole E (add z_0 z_1))
        "z-+")
   (--> (in-hole E (z_0 - z_1))
        (in-hole E (sub z_0 z_1))
        "z--")
   (--> (in-hole E (z_0 * z_1))
        (in-hole E (mul z_0 z_1))
        "z-*")
        )
       )

(render-language cyl)
(render-judgment-form types)
(render-reduction-relation cyl-whnf)

(judgment-holds
   (types () 4 τ)
   τ)

(traces cyl-whnf (term (case (inl Z 0) (x 1) (x 2)))) 

(traces cyl-whnf (term (cast (sym (id 0)) (box 0 4)))) 

(test--> cyl-whnf
         (term ((λ (x Z) x) 4)) (term 4))
(test--> cyl-whnf
         (term (tail (cons (box 0 4) (box 0 8)))) (term (box 0 8)))
(test--> cyl-whnf
         (term (cast (id 0) (box 0 4))) (term (box 0 4)))
