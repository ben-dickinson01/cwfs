{-# OPTIONS --without-K #-}

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

record ⊤ : Set where
    constructor tt

infix 1 _∼_
_∼_ : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : A → Set ℓ₂} → (f g : (a : A) → B a) → Set (ℓ₁ ⊔ ℓ₂)
_∼_ {A = A} f g = (x : A) → f x ≡ g x

postulate eq-htpy : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : A → Set ℓ₂} → (f g : (a : A) → B a) → f ∼ g → f ≡ g

ap : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : Set ℓ₂} → (f : A → B) → {x y : A} → (p : x ≡ y) → f x ≡ f y
ap f refl = refl

tr : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → (B : A → Set ℓ₂) → {x y : A} → (p : x ≡ y) → B x → B y
tr B refl ba = ba

inv : {ℓ₁ : Level} → {A : Set ℓ₁} → {x y : A} → (p : x ≡ y) → y ≡ x
inv refl = refl

concat : {ℓ₁ : Level} → {A : Set ℓ₁} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
concat refl refl = refl 