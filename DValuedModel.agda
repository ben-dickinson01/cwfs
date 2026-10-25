{-# OPTIONS --without-K --safe #-}

open import Prelude
open import UCwF

lone : Level
lone = lsuc lzero

D-model : (D : Set) → UCwF lone lzero lzero
D-model D .UCwF.Ctx = Set
D-model D .UCwF.Sub Δ Γ = Δ → Γ
D-model D .UCwF.id = λ x → x
D-model D .UCwF._∘_ = λ θ γ z → θ (γ z)
D-model D .UCwF.assoc-∘ = λ ξ θ γ → refl
D-model D .UCwF.left-unit-∘ = λ γ → refl
D-model D .UCwF.right-unit-∘ = λ γ → refl
D-model D .UCwF.𝟙 = ⊤
D-model D .UCwF.⟨⟩ = λ _ → tt
D-model D .UCwF.unique-⟨⟩ = λ γ → refl
D-model D .UCwF.Tm Γ = Γ → D
D-model D .UCwF._[_] = λ a γ z → a (γ z)
D-model D .UCwF.[id] = λ a → refl
D-model D .UCwF.[∘] = λ a θ γ → refl
D-model D .UCwF._▹ Γ = Γ × D
D-model D .UCwF.p Γ x = proj₁ x
D-model D .UCwF.q Γ x = proj₂ x
D-model D .UCwF.⟨_,_⟩ = λ γ a z → γ z , a z
D-model D .UCwF.▹-β₁ = λ γ a → refl
D-model D .UCwF.▹-β₂ = λ γ a → refl
D-model D .UCwF.▹-η = λ σ → refl
