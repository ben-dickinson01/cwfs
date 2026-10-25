{-
The record formalises categories with families (CwFs), following Definition 1
(Section 2.2.1) of Castellan, Clairambault and Dybjer's paper. The equations were
checked against the conversion rules in Section 5.1.2. Differences from the paper:
* γ : Sub Δ Γ for a morphism γ : Δ → Γ in C(Δ, Γ) (judgement form Δ ⊢ γ : Γ);
* Γ ▹ A where the paper writes Γ · A;
* 𝟙 where the paper writes 1 (Agda does not allow 1 as a name);
* superscripts ᵀ and ᵗ distinguish substitution in types and in terms;
* the functor T : Cᵒᵖ → Fam is split into Ty and Tm, each with its own substitution;
* comprehension is given by the operation ⟨_,_⟩ with β-laws and an η-law, rather than
  by the universal property (uniqueness of ⟨γ, a⟩); given the β-laws these are equivalent;
* equalities are propositional, so the term laws transport (tr) along the type laws;
* Sub, Ty and Tm are not required to be h-sets;
* the record takes four universe levels, since in the set model Ty Γ = Γ → Set lives in Set₁.
As in the paper, composition is applicative: θ ∘ γ means first γ, then θ.
-}

{-# OPTIONS --without-K --safe #-}

open import Prelude


record CwF (ℓc ℓs ℓty ℓtm : Level) : Set (lsuc (ℓc ⊔ ℓs ⊔ ℓty ⊔ ℓtm)) where
    infixl 9 _∘_
    infixl 5 _[_]ᵀ
    infixl 5 _[_]ᵗ
    infixl 4 _▹_
    field
        Ctx : Set ℓc
        Sub : (Δ Γ : Ctx) → Set ℓs
        id : {Γ : Ctx} → Sub Γ Γ
        _∘_ : {Δ Γ Θ : Ctx} → (θ : Sub Γ Θ) → (γ : Sub Δ Γ) → Sub Δ Θ
        -- ∘ laws
        assoc-∘ : {Δ Γ Θ Ξ : Ctx} → (ξ : Sub Θ Ξ) → (θ : Sub Γ Θ) → (γ : Sub Δ Γ) →
            ξ ∘ (θ ∘ γ) ≡ (ξ ∘ θ) ∘ γ
        left-unit-∘ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → id ∘ γ ≡ γ
        right-unit-∘ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → γ ∘ id ≡ γ
        -- 𝟙 terminal context (empty context) and associated laws
        𝟙 : Ctx
        ⟨⟩ : {Γ : Ctx} → Sub Γ 𝟙
        unique-⟨⟩ : {Γ : Ctx} → (γ : Sub Γ 𝟙) → γ ≡ ⟨⟩
        -- Type functor
        Ty : Ctx → Set ℓty
        _[_]ᵀ : {Δ Γ : Ctx} → (A : Ty Γ) → (γ : Sub Δ Γ) → Ty Δ
        [id]ᵀ : {Γ : Ctx} → (A : Ty Γ) → A [ id ]ᵀ ≡ A
        [∘]ᵀ : {Δ Γ Θ : Ctx} → (A : Ty Θ) → (θ : Sub Γ Θ) → (γ : Sub Δ Γ) → A [ θ ∘ γ ]ᵀ ≡ A [ θ ]ᵀ [ γ ]ᵀ
        -- Term functor
        Tm : (Γ : Ctx) → (A : Ty Γ) → Set ℓtm
        _[_]ᵗ : {Δ Γ : Ctx} → {A : Ty Γ} → Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]ᵀ)
        [id]ᵗ : {Γ : Ctx} → {A : Ty Γ} → (a : Tm Γ A) → tr (Tm Γ) ([id]ᵀ A) (a [ id ]ᵗ) ≡ a
        [∘]ᵗ : {Δ Γ Θ : Ctx} → {A : Ty Θ} → (a : Tm Θ A) → (θ : Sub Γ Θ) → (γ : Sub Δ Γ) →
            tr (Tm Δ) ([∘]ᵀ A θ γ) (a [ θ ∘ γ ]ᵗ) ≡ a [ θ ]ᵗ [ γ ]ᵗ
        -- Context comprehension
        _▹_ : (Γ : Ctx) → (A : Ty Γ) → Ctx
        p : (Γ : Ctx) → (A : Ty Γ) → Sub (Γ ▹ A) Γ
        q : (Γ : Ctx) → (A : Ty Γ) → Tm (Γ ▹ A) (A [ p Γ A ]ᵀ)
        ⟨_,_⟩ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → {A : Ty Γ} → (a : Tm Δ (A [ γ ]ᵀ)) → Sub Δ (Γ ▹ A)
        ▹-β₁ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → {A : Ty Γ} → (a : Tm Δ (A [ γ ]ᵀ)) → (p Γ A) ∘ ⟨ γ , a ⟩ ≡ γ
        ▹-β₂ : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → {A : Ty Γ} → (a : Tm Δ (A [ γ ]ᵀ)) →
            let path = concat (inv ([∘]ᵀ A (p Γ A) ⟨ γ , a ⟩ )) (ap (A [_]ᵀ) (▹-β₁ γ a)) in
            tr (Tm Δ) path (q Γ A [ ⟨ γ , a ⟩ ]ᵗ) ≡ a
        ▹-η : {Δ Γ : Ctx} → {A : Ty Γ} → (σ : Sub Δ (Γ ▹ A)) →
            let path = inv ([∘]ᵀ A (p Γ A) σ) in
            σ ≡ ⟨ p Γ A ∘ σ , tr (Tm Δ) path (q Γ A [ σ ]ᵗ) ⟩