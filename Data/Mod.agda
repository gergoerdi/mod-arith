open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ; zero; suc; _≤?_; _≥_)

import Data.Nat.Properties
open import Relation.Nullary.Decidable

module Data.Mod (n : ℕ) {≥2 : True (2 ≤? n)} where
private
  Repr : Set
  Repr = ℤ

module Dummy where
  module Definitions where
    open import Algebra.FunctionProperties using (Op₁; Op₂)
    open import Data.Integer renaming (+_ to ℤ+_; _+_ to _ℤ+_; _*_ to _ℤ*_; -_ to ℤ-_; _-_ to _ℤ-_)
    open import Relation.Binary

    [_] : ℕ → Repr
    [ n ] = ℤ+ n

    _+_ : Op₂ Repr
    _+_ = _ℤ+_

    -_ : Op₁ Repr
    -_ = ℤ-_

    _-_ : Op₂ Repr
    _-_ = _ℤ-_

    _*_ : Op₂ Repr
    _*_ = _ℤ*_

  -- open Definitions public

  module TheSetoid where
    open import Data.Integer
    open import Data.Nat.Divisibility
    open import Function using (_∘_; _⟨_⟩_)
    import Level

    open import Relation.Binary
    open import Relation.Binary.PropositionalEquality as P using (_≡_)

    import Data.Integer.Properties as Integer
    open import Algebra
    open CommutativeRing Integer.commutativeRing using (-‿inverse)
    open import Data.Product

    open import Data.Mod.Lemmas

    _∼_ : Rel ℤ _
    x ∼ y = n ∣ ∣ x - y ∣

    Mod : Setoid Level.zero Level.zero
    Mod = record
      { Carrier = ℤ
      ; _≈_ = _∼_
      ; isEquivalence = isEquivalence
      }
      where
        reflexive : Reflexive _∼_
        reflexive {x} = divides 0 (P.cong ∣_∣ (proj₂ -‿inverse x))

        symmetric : Symmetric _∼_
        symmetric {x} {y} (divides q eq) = divides q (abs-flip y x ⟨ P.trans ⟩ eq)

        transitive : Transitive _∼_
        transitive {x} {y} {z} d d′ = P.subst (_∣_ n) (P.cong ∣_∣ (telescope x y z)) (∣-abs-+ (x - y) (y - z) d d′)

        abstract
          isEquivalence : IsEquivalence _∼_
          isEquivalence = record
            { refl = λ {x} → reflexive {x}
            ; sym = λ {x} {y} → symmetric {x} {y}
            ; trans = λ {x} {y} {z} → transitive {x} {y} {z}
            }

  module Soundness where
    open Definitions

    open import Relation.Binary
    open Setoid TheSetoid.Mod

    open import Algebra.FunctionProperties using (Op₁; Op₂)

    open import Relation.Binary.PropositionalEquality as P using (_≡_)
    open import Data.Nat.Divisibility
    open import Function using (_∘_; _⟨_⟩_)
    open import Data.Integer using (∣_∣)
    open import Data.Mod.Lemmas
    import Data.Integer.Properties as Integer
    open import Data.Integer renaming (_+_ to _ℤ+_; _*_ to _ℤ*_; -_ to ℤ-_; _-_ to _ℤ-_)

    Sound₁ : Op₁ Repr → Set
    Sound₁ f = f Preserves _≈_ ⟶ _≈_

    Sound₂ : Op₂ Repr → Set
    Sound₂ ∙ = ∙ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

    abstract
      plus-sound : Sound₂ _+_
      plus-sound {x} {x′} {y} {y′} x∼x′ y∼y′ = P.subst (_∣_ n ∘ ∣_∣) (P.sym (eq x x′ y y′))
                                                       (∣-abs-+ (x - x′) (y - y′) x∼x′ y∼y′)
        where
        abstract
          open Integer.RingSolver
          eq : ∀ a b c d → (a + c) - (b + d) ≡ (a - b) + (c - d)
          eq = solve 4 (λ a b c d → (a :+ c) :- (b :+ d) := (a :- b) :+ (c :- d)) P.refl

      neg-sound : Sound₁ -_
      neg-sound {x} {x′} x∼x′ = ∣-abs-neg x x′ x∼x′

      minus-sound : Sound₂ _-_
      minus-sound {x} {x′} {y} {y′} x∼x y∼y′ = P.subst (_∣_ n ∘ ∣_∣) (P.sym (eq x x′ y y′))
                                                       (∣-abs‿- (x - x′) (y - y′) x∼x y∼y′)
        where
        abstract
          open Integer.RingSolver
          eq : ∀ a b c d → (a - c) - (b - d) ≡ (a - b) - (c - d)
          eq = solve 4 (λ a b c d → (a :- c) :- (b :- d) := (a :- b) :- (c :- d)) P.refl

      mul-sound : Sound₂ _*_
      mul-sound {x} {x′} {y} {y′} x∼x′ y∼y′ = P.subst (_∣_ n ∘ ∣_∣) (P.sym (eq x x′ y y′))
                                                      (∣-abs-+ (x * (y - y′)) ((x - x′) * y′)
                                                              (∣-abs-*ˡ x (y - y′) y∼y′)
                                                              (∣-abs-*ʳ (x - x′) y′ x∼x′))
        where
        abstract
          open Integer.RingSolver
          eq : ∀ a b c d → a ℤ* c ℤ- b ℤ* d ≡ a ℤ* (c ℤ- d) ℤ+ (a ℤ- b) ℤ* d
          eq = solve 4 (λ a b c d → a :* c :- b :* d := a :* (c :- d) :+ (a :- b) :* d) P.refl

open Dummy using (module Definitions; module TheSetoid; module Soundness)
open Definitions public
open TheSetoid public
open Soundness public
