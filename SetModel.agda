{-# OPTIONS --without-K --safe #-}

open import Prelude
open import CwF

lone : Level
lone = lsuc lzero

set-model : CwF lone lzero lone lzero
set-model .CwF.Ctx = Set
set-model .CwF.Sub Δ Γ = Δ → Γ
set-model .CwF.id = λ x → x
set-model .CwF._∘_ = λ θ γ x → θ (γ x)
set-model .CwF.assoc-∘ ξ θ γ = refl
set-model .CwF.left-unit-∘ γ = refl
set-model .CwF.right-unit-∘ γ = refl
set-model .CwF.𝟙 = ⊤
set-model .CwF.⟨⟩ = λ x → tt
set-model .CwF.unique-⟨⟩ γ = refl
set-model .CwF.Ty Γ = Γ → Set
set-model .CwF._[_]ᵀ A γ = λ x → A (γ x)
set-model .CwF.[id]ᵀ = λ A → refl
set-model .CwF.[∘]ᵀ = λ A θ γ → refl
set-model .CwF.Tm Γ A = (x : Γ) → A x
set-model .CwF._[_]ᵗ a γ x = a (γ x)
set-model .CwF.[id]ᵗ = λ a → refl
set-model .CwF.[∘]ᵗ = λ a θ γ → refl
set-model .CwF._▹_ Γ A = Σ Γ A
set-model .CwF.p = λ Γ A z → z .proj₁
set-model .CwF.q = λ Γ A z → z .proj₂
set-model .CwF.⟨_,_⟩ = λ γ a z → γ z , a z
set-model .CwF.▹-β₁ = λ γ a → refl
set-model .CwF.▹-β₂ = λ γ a → refl
set-model .CwF.▹-η = λ σ → refl