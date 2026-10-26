{-
Π-types as extra structure on a CwF, following Definition 28 (Section 5.3.1) of
Castellan, Clairambault and Dybjer's paper. Differences from the paper:
* Π-structure is a separate record parameterised by a CwF, rather than extra fields
  of CwF, so that CwFs without Π-types (such as those from UCwF-to-CwF) are unaffected;
* application is unary, app : Tm Γ (Π A B) → Tm (Γ ▹ A) B, where the paper's ap is binary;
  the two are interdefinable (ap(f, a) = app f [⟨id, a⟩]), and the unary form avoids a
  transport along [id]ᵀ, so β and η need no transport;
* the lifted substitution γ ↑ A is the paper's ⟨γ ∘ p, q⟩; since equalities are
  propositional, q is transported along [∘]ᵀ to have the type the pairing needs;
* the substitution law for lam is transported along Π[]; the law for application
  follows from it together with β and η, so it is not a field.
-}

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