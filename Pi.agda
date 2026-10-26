{-# OPTIONS --without-K --safe #-}

open import Prelude
open import CwF

module _ {ℓc ℓs ℓty ℓtm : Level} (C : CwF ℓc ℓs ℓty ℓtm) where
    open CwF.CwF C

    _↑_ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → (A : Ty Γ) → Sub (Δ ▹ A [ γ ]ᵀ) (Γ ▹ A)
    _↑_ {Δ} {Γ} γ A = 
        ⟨ γ ∘ p _ (A [ γ ]ᵀ) , tr (Tm (Δ ▹ A [ γ ]ᵀ)) (inv ([∘]ᵀ A γ (p _ (A [ γ ]ᵀ)))) (q _ (A [ γ ]ᵀ)) ⟩ 

    record Π-structure : Set (ℓc ⊔ ℓs ⊔ ℓty ⊔ ℓtm) where
        field
            Π : {Γ : Ctx} → (A : Ty Γ) → (B : Ty (Γ ▹ A)) → Ty Γ
            lam : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ ▹ A)} → Tm (Γ ▹ A) B → Tm Γ (Π A B)
            app : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ ▹ A)} → Tm Γ (Π A B) → Tm (Γ ▹ A) B
            Π-β : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ ▹ A)} → (t : Tm (Γ ▹ A) B) → app (lam t) ≡ t
            Π-η : {Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ ▹ A)} → (f : Tm Γ (Π A B)) → lam (app f) ≡ f
            Π[] : {Δ Γ : Ctx} → (A : Ty Γ) → (B : Ty (Γ ▹ A)) → (γ : Sub Δ Γ) → 
                Π A B [ γ ]ᵀ ≡ Π (A [ γ ]ᵀ) (B [ γ ↑ A ]ᵀ)
            lam[] : {Δ Γ : Ctx} → {A : Ty Γ} → {B : Ty (Γ ▹ A)} → (γ : Sub Δ Γ) → (t : Tm (Γ ▹ A) B) → 
                tr (Tm Δ) (Π[] A B γ) (lam t [ γ ]ᵗ) ≡ lam (t [ γ ↑ A ]ᵗ)