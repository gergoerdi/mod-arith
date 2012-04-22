open import Relation.Binary

module Quotient.Op {c l} (A : Setoid c l) where

private
  module Dummy where
    open import Quotient
    open import Function
    open import Algebra.FunctionProperties using (Op₁; Op₂)
    open import Data.Product

    open Setoid A renaming (Carrier to A₀)

    lift₁ : (f : Op₁ A₀) → f Preserves _≈_ ⟶ _≈_
          → Op₁ (Quotient A)
    lift₁ f P = rec _ (λ x → [ f x ]) (λ x≈y → [ P x≈y ]-cong)

    private
      open import Relation.Binary.PropositionalEquality using (Extensionality)
      open import Level using (suc) renaming (zero to ℓ₀)
      postulate
        extensionality : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′

    open import Relation.Binary.PropositionalEquality using (proof-irrelevance; _≡_)

    Sound₂ : Op₂ A₀ → Set _
    Sound₂ ∙ = ∙ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

    LiftOp₂ : Set _
    LiftOp₂ = ∃ λ ∙ → Sound₂ ∙

    lift₂ : (∙ : LiftOp₂) → Op₂ (Quotient A)
    lift₂ (_∙_ , prf) = rec A (λ x → rec _ (λ y → [ x ∙ y ])
                              (λ t≈u → [ prf refl t≈u ]-cong))
                              (λ x≈y → extensionality
                              (elim _ _ (λ _ → [ prf x≈y refl ]-cong)
                              (λ _ → proof-irrelevance _ _)))

{-
    import Algebra.FunctionProperties as FunProp
    open FunProp (_≡_ {A = Quotient A})

    lift-comm : (_∙_ : Op₂ A₀) → (P : Sound₂ _∙_) → (prf : ∀ x y → x ∙ y ≈ y ∙ x) → Commutative (lift₂ _∙_ P)
    lift-comm ∙ P prf = elim A _ (λ x → elim A _ (λ y → [ prf x y ]-cong)
                             (λ _ → proof-irrelevance _ _))
                             (λ _ → extensionality (λ _ → proof-irrelevance _ _))
-}
open Dummy public

