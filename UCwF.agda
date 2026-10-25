{-# OPTIONS --without-K --safe #-}

open import Prelude

record UCwF (ℓc ℓs ℓtm : Level) : Set (lsuc (ℓc ⊔ ℓs ⊔ ℓtm)) where
    infixl 9 _∘_
    infixl 5 _[_]
    infix 4 _▹
    field
        Ctx : Set ℓc
        Sub : (Δ Γ : Ctx) → Set ℓs
        id : {Γ : Ctx} → Sub Γ Γ
        _∘_ : {Δ Γ Θ : Ctx} → (θ : Sub Γ Θ) → (γ : Sub Δ Γ) → Sub Δ Θ
        -- ∘ laws
        assoc-∘ : {Δ Γ Θ Ξ : Ctx} → (ξ : Sub Θ Ξ) → (θ : Sub Γ Θ) → (γ : Sub Δ Γ)  → ξ ∘ (θ ∘ γ) ≡ (ξ ∘ θ) ∘ γ 
        left-unit-∘ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → id ∘ γ ≡ γ
        right-unit-∘ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → γ ∘ id ≡ γ
        -- 𝟙 terminal context (empty context) and associated laws
        𝟙 : Ctx
        ⟨⟩ : {Γ : Ctx} → Sub Γ 𝟙
        unique-⟨⟩ : {Γ : Ctx} → (γ : Sub Γ 𝟙) → γ ≡ ⟨⟩
        -- Term functor
        Tm : (Γ : Ctx) → Set ℓtm
        _[_] : {Δ Γ : Ctx} → Tm Γ → (γ : Sub Δ Γ) → Tm Δ 
        [id] : {Γ : Ctx} → (a : Tm Γ) → a [ id ] ≡ a
        [∘] : {Δ Γ Θ : Ctx} → (a : Tm Θ) → (θ : Sub Γ Θ) → (γ : Sub Δ Γ) → a [ θ ∘ γ ] ≡ a [ θ ] [ γ ]
        -- Context comprehension 
        _▹ : Ctx → Ctx
        p : (Γ : Ctx) → Sub (Γ ▹) Γ
        q : (Γ : Ctx) → Tm (Γ ▹)
        ⟨_,_⟩ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → (a : Tm Δ) → Sub Δ (Γ ▹) 
        ▹-β₁ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → (a : Tm Δ) → (p Γ) ∘ ⟨ γ , a ⟩ ≡ γ
        ▹-β₂ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → (a : Tm Δ ) →  q Γ [ ⟨ γ , a ⟩ ] ≡ a  
        ▹-η : {Δ Γ : Ctx} →  (σ : Sub Δ (Γ ▹)) → σ ≡ ⟨ p Γ ∘ σ , q Γ [ σ ] ⟩ 