#lang racket
(require redex)

; Simple calculus loosely based around Tarski's cylindrical logic
; and Monadic Boolean algebra and Interior algebra
; and S5 Modal logic

(define-language cyl
  (z integer)
  ; Think of κ as pointer/an index into an array of quantifiers
  (κ natural)

  (τ ∅ ⊤ (τ → τ) (τ + τ) (τ × τ)
     
     ; Possibly, like existential
     (◇ κ τ)
     ; Necessarily, like universal
     (□ κ τ)

     (κ = κ)
     Z)
  
  (v x
     !
     (λ (x τ) e)

     (e Δ e)
     (inl τ e) (inr τ e)

     (nec κ v)
     (box κ v)
    
     (id κ)
     z)

  (e v
     (absurd τ e)

     (e e)

     (fst e)
     (snd e)

     (case e (x e) (x e))

     (nec κ e)
     (box κ e)

     (let (x e) e)

     (T e)
     (K e e)
     (dup e)

     (□-comm e)
     (◇-comm e)

     (e ∘ e)
     (sym e)
     (cast e e)
     
     (e + e)
     (e - e)
     (e × e)
     )

  (x variable-not-otherwise-mentioned)
 
  #:binding-forms
  (λ (x τ) e #:refers-to x)
  (case e (x e #:refers-to x) (x e #:refers-to x))
  (let (x e) e #:refers-to x))

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

  ; Empty Set
  [(types Γ e ∅)
   -------------------------
   (types Γ (absurd τ e) τ)]  

  ; Point
  [-------------------------
   (types Γ ! ⊤)]
  
  ; Product
  [(types Γ e_0 τ_0) (types Γ e_1 τ_1)
   -------------------------
   (types Γ (e_0 Δ e_1) (τ_0 × τ_1))]  
  [(types Γ e (τ_0 × τ_1))
   -------------------------
   (types Γ (fst e) τ_0)]  
  [(types Γ e (τ_0 × τ_1))
   -------------------------
   (types Γ (snd e) τ_1)]  
  
  ; Sum
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

  ; Universal
  [(types () e τ)
   -------------------------
   (types Γ (nec κ e) (□ κ τ))]
  
  [(types Γ e (□ κ τ))
   -------------------------
   (types Γ (T e) τ)]
  
  [(types Γ e_0 (□ κ (τ_0 → τ_1)))
   (types Γ e_1 (□ κ τ_0))
   -------------------------
   (types Γ (K e_0 e_1) (□ κ τ_1))]

  [(types Γ e (□ κ τ))
   -------------------------
   (types Γ (dup e) (□ κ (□ κ τ)))]

  ; Existentials
  ; yes the M-word
 
  [(types Γ e τ)
    -------------------------
   (types Γ (box κ e) (◇ κ τ))]

  [(types (p ...) e_0 (◇ κ τ_0))
   (types ([x : τ_0] p ...) e_1 (◇ κ τ_1))
    -------------------------
   (types (p ...) (let (x e_0) e_1) (◇ κ τ_1))]

  ; Commutativity of existentials/universals
   
  [(types Γ e (□ κ_1 (□ κ_0 τ)))
    -------------------------
   (types Γ (□-comm e) (□ κ_0 (□ κ_1 τ)))]

  [(types Γ e (◇ κ_1 (◇ κ_0 τ)))
    -------------------------
   (types Γ (◇-comm e) (◇ κ_0 (◇ κ_1 τ)))]

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
   (types Γ (e_0 × e_1) Z)]
)

(define-extended-language cyl+stk cyl
  (E hole
     (absurd E)

     (E e)

     (fst E)
     (snd E)

     (case E (x e) (x e))

     (nec κ E)
     (box κ E)

     (T E)
     (dup E)
     (K E e) (K v E)

     (let (x E) e)

     (□-comm E)
     (◇-comm E)

     (v ∘ E) (E ∘ e)
     (sym E)
     (cast E e) (cast v E)

     (E + e) (v + E)
     (E - e) (v - E)
     (E × e) (v × E)
    )
  
  #:binding-forms
  (case E (x e #:refers-to x) (x e #:refers-to x))
  (let (x E) e #:refers-to x)
  )

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
        "→-subst")

   (--> (in-hole E (fst (e_0 Δ e_1)))
        (in-hole E e_0)
        "×-fst")
   (--> (in-hole E (snd (e_0 Δ e_1)))
        (in-hole E e_1)
        "×-snd")

   (--> (in-hole E (case (inl τ e_0) (x_0 e_1) (x_1 e_2)))
        (in-hole E (substitute e_1 x_0 e_0))
        "+-case-inl")
   (--> (in-hole E (case (inr τ e_0) (x_0 e_1) (x_1 e_2)))
        (in-hole E (substitute e_2 x_1 e_0))
        "+-case-inr")
   
   (--> (in-hole E (T (nec κ e)))
        (in-hole E e)
        "□-T")
   (--> (in-hole E (K (nec κ e_0) (nec κ e_1)))
        (in-hole E (nec κ (e_0 e_1)))
        "□-K")
   (--> (in-hole E (dup (nec κ e)))
        (in-hole E (nec κ (nec κ e)))
        "□-dup")
   
   (--> (in-hole E (□-comm (nec κ_0 (nec κ_1 e))))
        (in-hole E (nec κ_1 (nec κ_0 e)))
        "□-comm")

   (--> (in-hole E (let (x (box κ e_0)) e_1))
        (in-hole E (substitute e_1 x e_0))
        "◇-let")
   (--> (in-hole E (◇-comm (box κ_0 (box κ_1 e))))
        (in-hole E (box κ_1 (box κ_0 e)))
        "◇-comm")

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
   (--> (in-hole E (z_0 × z_1))
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
         (term (cast (id 0) (box 0 4))) (term (box 0 4)))
