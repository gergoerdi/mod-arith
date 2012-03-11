module Quotient.Product where

open import Quotient
open import Relation.Binary
open import Function
open import Algebra.FunctionProperties using (Op₁; Op₂)

private
  module Dummy₁ {c l} {A : Setoid c l} where
    open Setoid A renaming (Carrier to A₀)

    lift₁ : (f : Op₁ A₀) → f Preserves _≈_ ⟶ _≈_
          → Op₁ (Quotient A)
    lift₁ f P = rec _ ([_] ∘ f) (λ x≈y → [ P x≈y ]-cong)
open Dummy₁ public

open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Product.Pointwise

_×-quot_ : ∀ {c l c′ l′} → (A : Setoid c l) → (B : Setoid c′ l′) → Set _
A ×-quot B = Quotient (A ×-setoid B)

private
  open import Relation.Binary.PropositionalEquality using (Extensionality)
  open import Level using (suc) renaming (zero to ℓ₀)
  postulate
    extensionality : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′

curry-quot : ∀ {c ℓ ℓ′} → ∀ {A B : Setoid c ℓ} {C : Set ℓ′}
           → (A ×-quot B → C) → (Quotient A → Quotient B → C)
curry-quot {A = A} {B = B} {C = C} f =
  rec _ f₁ (λ x∼y → extensionality (elim _ (λ t → lem x∼y t) (λ x∼y → proof-irrelevance _ _)))
  where
  module SA = Setoid A
  module SB = Setoid B
  module SP = Setoid (A ×-setoid B)

  f₁ : Setoid.Carrier A → Quotient B → C
  f₁ x = rec _ (λ t → f [ x , t ]) (λ t≈u → cong f [ SA.refl , t≈u ]-cong)

  lem : {x y : Setoid.Carrier A} → (x∼y : SA._≈_ x y) → ∀ t → f₁ x [ t ] ≡ f₁ y [ t ]
  lem {x} {y} x∼y t = cong f [ (x∼y , SB.refl) ]-cong

private
  module Dummy₂ {c l} {A : Setoid c l} where
    open Setoid A renaming (Carrier to A₀)

    lift₂ : (f : Op₂ A₀) → f Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
          → Op₂ (Quotient A)
    lift₂ f P = curry-quot f′
      where
      f′ : A ×-quot A → Quotient A
      f′ = rec _ ([_] ∘ uncurry f) (λ {xt} {yu} eq → [ (P (proj₁ eq) (proj₂ eq)) ]-cong)
open Dummy₂ public

