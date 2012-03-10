module Quotient.Product where

open import Quotient
open import Data.Product
open import Relation.Binary -- using (Setoid)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Product.Pointwise

_×-quot_ : ∀ {c l c′ l′} → (A : Setoid c l) → (B : Setoid c′ l′) → Set _
A ×-quot B = Quotient (A ×-setoid B)

private
  open import Relation.Binary.PropositionalEquality using (Extensionality)
  open import Level using () renaming (zero to ℓ₀)
  postulate
    extensionality : Extensionality ℓ₀ ℓ₀

curry-quot : ∀ {A B : Setoid ℓ₀ _} {C : Set} → (A ×-quot B → C) → (Quotient A → Quotient B → C)
curry-quot {A} {B} {C} f = rec _ f₁ (λ x∼y → extensionality (elim _ (λ t → lem x∼y t) (λ x∼y → proof-irrelevance _ _)))
  where
  module SA = Setoid A
  module SB = Setoid B
  module SP = Setoid (A ×-setoid B)

  f₁ : Setoid.Carrier A → Quotient B → C
  f₁ x = rec _ (λ t → f [ x , t ]) (λ t≈u → cong f [ SA.refl , t≈u ]-cong)

  lem : {x y : Setoid.Carrier A} → (x∼y : SA._≈_ x y) → ∀ t → f₁ x [ t ] ≡ f₁ y [ t ]
  lem {x} {y} x∼y t = cong f [ (x∼y , SB.refl) ]-cong
