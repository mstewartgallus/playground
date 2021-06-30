#lang racket
(require redex)

;; A simple playground for playing around with coexponential types
;; Sort of dual to exponentials

(define-language coexp
  (O · ∅ (O × O) (O + O) (O - O) Z)
  (τ [O → O])
  (f O (f ∘ f)
     x
     integer

     (! f)
     (jump f)

     (f push f)
     (κ (x · → O) f)

     (f copush f)
     (κ (x O → ∅) f)

     (f copass f)
     (ζ (x O → ∅) f)
     )
  (x variable-not-otherwise-mentioned)
 
  #:binding-forms
  (κ (x · → O) f #:refers-to x)
  (κ (x O → ∅) f #:refers-to x)
  (ζ (x O → ∅) f #:refers-to x))

(define-extended-language coexp+Γ coexp
  [Γ () (p ...)]
  [p [x : O → O]])

(define-judgment-form coexp+Γ
  #:mode (types I I O)
  #:contract (types Γ f τ)
 
  [-------------------------
   (types Γ O (O → O))]

  [(types Γ f_0 (O_1 → O_2)) (types Γ f_1 (O_0 → O_1))
   -------------------------
   (types Γ (f_0 ∘ f_1) (O_0 → O_2))]

  
  [-------------------------
   (types Γ integer (· → Z))]

  
  [(types Γ f (O_0 → O_1))
   -------------------------
   (types Γ (! f) (O_0 → ·))]

  [(types Γ f (O_1 → O_0))
   -------------------------
   (types Γ (jump f) (∅ → O_1))]


  [(types Γ f_0 ((O_0 × O_1) → O_2)) (types Γ f_1 (· → O_1))
   -------------------------
   (types Γ (f_0 push f_1) (O_0 → O_2))]  

  [(types ([x : · → O_0] p ...) f (O_1 → O_2))
   -------------------------
   (types (p ...) (κ (x · → O_0) f) ((O_1 × O_0) → O_2))]
  

  [(types Γ f_0 (O_2 → (O_0 + O_1))) (types Γ f_1 (O_1 → ∅))
   -------------------------
   (types Γ (f_0 copush f_1) (O_2 → O_0))]
  
  [(types ([x : O_0 → ∅] p ...) f (O_2 → O_1))
   -------------------------
   (types (p ...) (κ (x O_0 → ∅) f) (O_2 → (O_1 + O_0) ))]


  [(types Γ f_0 ((O_2 - O_1) → O_0)) (types Γ f_1 (O_1 → ∅))
   -------------------------
   (types Γ (f_0 copass f_1) (O_2 → O_0))]
  [(types ([x : O_0 → ∅] p ...) f (O_2 → O_1))
   -------------------------
   (types (p ...) (ζ (x O_0 → ∅) f) ((O_2 - O_0) → O_1 ))]
)

(define coexp-whnf
  (reduction-relation coexp #:domain f
   (--> (O ∘ f) f "id-left")
   (--> (f ∘ O) f "id-right")

   (--> ((! f_0) ∘ f_1)
        (! (f_0 ∘ f_1))
        "!-left")
   (--> (f_1 ∘ (jump f_0))
        (jump (f_1 ∘ f_0))
        "jump-right")

   (--> ((κ (x · → O) f_0) push f_1)
        (substitute f_1 x f_0)
        "κ-lift")
   (--> ((κ (x O → ∅) f_0) copush f_1)
        (substitute f_1 x f_0)
        "κ-copush")

   (--> ((ζ (x O → ∅) f_0) copass f_1)
        (substitute f_1 x f_0)
        "ζ-copass")))

(define-extended-language coexp-cbv coexp
    (F hole
     (F ∘ f)
     (f ∘ F)
     (κ (x · → O) F)
     (κ (x O → ∅) F)
     (ζ (x O → ∅) F)
     )
  #:binding-forms
  (κ (x · → O) F #:refers-to x)
  (κ (x O → ∅) F #:refers-to x)
  (ζ (x O → ∅) F #:refers-to x)
  )

(render-language coexp)
(render-judgment-form types)
(render-reduction-relation coexp-whnf)

(judgment-holds
   (types () 4 τ)
   τ)
(judgment-holds
   (types () ((κ (x · → Z) (· push 4)) push 4) τ)
   τ)

(test-->
 coexp-whnf
 (term (· ∘ ·)) (term ·))
