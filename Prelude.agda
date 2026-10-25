{-# OPTIONS --without-K --safe #-}

open import Agda.Primitive public

infix 4 _≡_
data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ 
    where
        refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

infixr 8 _,_
record Σ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    field
        proj₁ : A
        proj₂ : B proj₁

open Σ public

infixr 2 _×_
_×_ : {ℓ₁ ℓ₂ : Level} → (A : Set ℓ₁) → (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ A (λ _ → B)

record ⊤ : Set where
    constructor tt

ap : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : Set ℓ₂} → (f : A → B) → {x y : A} → (p : x ≡ y) → f x ≡ f y
ap f refl = refl

tr : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → (B : A → Set ℓ₂) → {x y : A} → (p : x ≡ y) → B x → B y
tr B refl ba = ba

tr-const : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → (B : Set ℓ₂) → {x y : A} → (p : x ≡ y) → (b : B) → tr (λ _ → B) p b ≡ b
tr-const B refl b = refl

inv : {ℓ₁ : Level} → {A : Set ℓ₁} → {x y : A} → (p : x ≡ y) → y ≡ x
inv refl = refl

concat : {ℓ₁ : Level} → {A : Set ℓ₁} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
concat refl refl = refl 