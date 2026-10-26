{-
The set model of CwFs: more precisely, the standard model in Agda's universe Set,
whose "sets" are arbitrary types rather than h-sets.
* contexts are types in Set, and substitutions are functions;
* the terminal context is ⊤;
* a type over Γ is a family Γ → Set, and substitution in types is precomposition;
* a term of type A over Γ is a dependent function (x : Γ) → A x;
* context comprehension Γ ▹ A is the Σ-type Σ Γ A, with p and q the projections;
* Π A B at x is Agda's dependent function type (a : A x) → B (x , a), with lam and
  app given by currying and uncurrying.
Every law holds by refl, including the Π-laws: substitution is composition, and
functions, ⊤ and Σ have definitional η. In particular all the transports in the term
laws, and the one in the lifted substitution γ ↑ A, reduce away.
-}

{-# OPTIONS --without-K --safe #-}

open import Prelude
open import CwF
open import Pi

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

Π-set-model : Π-structure set-model
Π-set-model .Π-structure.Π A B x = (a : A x) → B (x , a)
Π-set-model .Π-structure.lam = λ t x a → t (x , a)
Π-set-model .Π-structure.app = λ f z → f (z .proj₁) (z .proj₂)
Π-set-model .Π-structure.Π-β = λ t → refl
Π-set-model .Π-structure.Π-η = λ f → refl
Π-set-model .Π-structure.Π[] = λ A B γ → refl
Π-set-model .Π-structure.lam[] = λ γ t → refl