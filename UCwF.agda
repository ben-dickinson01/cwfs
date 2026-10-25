{-# OPTIONS --without-K --safe #-}

open import Prelude
open import CwF

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
        ▹-β₂ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → (a : Tm Δ ) → q Γ [ ⟨ γ , a ⟩ ] ≡ a
        ▹-η : {Δ Γ : Ctx} →  (σ : Sub Δ (Γ ▹)) → σ ≡ ⟨ p Γ ∘ σ , q Γ [ σ ] ⟩

module _ {ℓc ℓs ℓtm : Level} (U : UCwF ℓc ℓs ℓtm) where
    open UCwF U

    UCwF-to-CwF : CwF ℓc ℓs lzero ℓtm
    UCwF-to-CwF .CwF.Ctx = Ctx
    UCwF-to-CwF .CwF.Sub = Sub
    UCwF-to-CwF .CwF.id = id
    UCwF-to-CwF .CwF._∘_ = _∘_
    UCwF-to-CwF .CwF.assoc-∘ = assoc-∘
    UCwF-to-CwF .CwF.left-unit-∘ = left-unit-∘
    UCwF-to-CwF .CwF.right-unit-∘ = right-unit-∘
    UCwF-to-CwF .CwF.𝟙 = 𝟙
    UCwF-to-CwF .CwF.⟨⟩ = ⟨⟩
    UCwF-to-CwF .CwF.unique-⟨⟩ = unique-⟨⟩
    UCwF-to-CwF .CwF.Ty = λ Γ → ⊤
    UCwF-to-CwF .CwF._[_]ᵀ = λ A γ → tt
    UCwF-to-CwF .CwF.[id]ᵀ = λ A → refl
    UCwF-to-CwF .CwF.[∘]ᵀ = λ A θ γ → refl
    UCwF-to-CwF .CwF.Tm Γ A = Tm Γ
    UCwF-to-CwF .CwF._[_]ᵗ = _[_]
    UCwF-to-CwF .CwF.[id]ᵗ = [id]
    UCwF-to-CwF .CwF.[∘]ᵗ = [∘]
    UCwF-to-CwF .CwF._▹_ Γ A = Γ ▹
    UCwF-to-CwF .CwF.p Γ A = p Γ
    UCwF-to-CwF .CwF.q = λ Γ A → q Γ
    UCwF-to-CwF .CwF.⟨_,_⟩ = λ γ {A} → ⟨_,_⟩ γ
    UCwF-to-CwF .CwF.▹-β₁ = λ γ {A} → ▹-β₁ γ
    UCwF-to-CwF .CwF.▹-β₂ {Δ} {Γ} γ {A} a = 
            concat 
                (tr-const  
                    (UCwF-to-CwF .CwF.Tm Δ _) 
                    _
                    (q Γ [ ⟨ γ , a ⟩ ])) 
                (▹-β₂ γ a)
    UCwF-to-CwF .CwF.▹-η = ▹-η