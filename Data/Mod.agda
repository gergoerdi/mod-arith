module Data.Mod where

open import Data.Nat using (ℕ) renaming (_*_ to _ℕ*_)

module Dummy {n : ℕ} where
  open import Data.Integer
  open import Data.Nat.Divisibility
  open import Function using (_∘_; _⟨_⟩_)
  import Level

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as P using (_≡_)

  open import Algebra
  import Data.Integer.Properties as Integer
  open CommutativeRing Integer.commutativeRing using (-‿inverse; 1#; 0#)
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

  private
    open Setoid Mod

    open import Algebra.FunctionProperties using (Op₁; Op₂)

    Sound₂ : Op₂ Carrier → Set
    Sound₂ ∙ = ∙ Preserves₂ _∼_ ⟶ _∼_ ⟶ _∼_

  open Integer.RingSolver

  plus : Op₂ Carrier
  plus = _+_

  minus : Op₂ Carrier
  minus = _-_

  mul : Op₂ Carrier
  mul = _*_

  abstract
    plus-sound : Sound₂ plus
    plus-sound {x} {x′} {y} {y′} x∼x′ y∼y′ = P.subst (_∣_ n ∘ ∣_∣) (P.sym (eq x x′ y y′))
                                                     (∣-abs-+ (x - x′) (y - y′) x∼x′ y∼y′)
      where
      abstract
        eq : ∀ a b c d → (a + c) - (b + d) ≡ (a - b) + (c - d)
        eq = solve 4 (λ a b c d → (a :+ c) :- (b :+ d) := (a :- b) :+ (c :- d)) P.refl

    minus-sound : Sound₂ minus
    minus-sound {x} {x′} {y} {y′} x∼x y∼y′ = P.subst (_∣_ n ∘ ∣_∣) (P.sym (eq x x′ y y′))
                                                     (∣-abs‿- (x - x′) (y - y′) x∼x y∼y′)
      where
      abstract
        eq : ∀ a b c d → (a - c) - (b - d) ≡ (a - b) - (c - d)
        eq = solve 4 (λ a b c d → (a :- c) :- (b :- d) := (a :- b) :- (c :- d)) P.refl

    mul-sound : Sound₂ mul
    mul-sound {x} {x′} {y} {y′} x∼x′ y∼y′ = P.subst (_∣_ n ∘ ∣_∣) (P.sym (eq x x′ y y′))
                                                    (∣-abs-+ (x * (y - y′)) ((x - x′) * y′)
                                                            (∣-abs-*ˡ x (y - y′) y∼y′)
                                                            (∣-abs-*ʳ (x - x′) y′ x∼x′))
      where
      abstract
       eq : ∀ a b c d → a * c - b * d ≡ a * (c - d) + (a - b) * d
       eq = solve 4 (λ a b c d → a :* c :- b :* d := a :* (c :- d) :+ (a :- b) :* d) P.refl


  module Properties where
    import Algebra.FunctionProperties as FunProp
    open FunProp (_∼_)

    import Data.Integer.Properties as Integer
    private
      module ℤ-CR = CommutativeRing Integer.commutativeRing

    open import Algebra.Structures

    plus-isCommutativeMonoid : IsCommutativeMonoid _∼_ plus (+ 0)
    plus-isCommutativeMonoid = record
      { isSemigroup = isSemigroup
      ; identityˡ = plus-identityˡ
      ; comm = plus-comm
      }
      where
      abstract
        module S = Setoid Mod

        isSemigroup : IsSemigroup _∼_ plus
        isSemigroup = record
          { isEquivalence = S.isEquivalence
          ; assoc = λ x y z → S.reflexive (ℤ-CR.+-assoc x y z)
          ; ∙-cong = λ {x x′ y y′} x∼x′ y∼y′ → plus-sound {x} {x′} {y} {y′} x∼x′ y∼y′
          }

        plus-identityˡ : LeftIdentity (+ 0) plus
        plus-identityˡ = λ x → S.reflexive (proj₁ ℤ-CR.+-identity x)

        plus-comm : Commutative plus
        plus-comm = λ x y → S.reflexive (ℤ-CR.+-comm x y)

    mul-isMonoid : IsMonoid _∼_ mul (+ 1)
    mul-isMonoid = record
      { isSemigroup = isSemigroup
      ; identity = mul-identityˡ , mul-identityʳ
      }
      where
      abstract
        module S = Setoid Mod

        isSemigroup : IsSemigroup _∼_ mul
        isSemigroup = record
          { isEquivalence = S.isEquivalence
          ; assoc = λ x y z → S.reflexive (ℤ-CR.*-assoc x y z)
          ; ∙-cong = λ {x x′ y y′} x∼x′ y∼y′ → mul-sound {x} {x′} {y} {y′} x∼x′ y∼y′
          }

        mul-identityˡ : LeftIdentity (+ 1) mul
        mul-identityˡ = λ x → S.reflexive (proj₁ ℤ-CR.*-identity x)

        mul-identityʳ : RightIdentity (+ 1) mul
        mul-identityʳ = λ x → S.reflexive (proj₂ ℤ-CR.*-identity x)

open Dummy public renaming (plus to _+_; minus to _-_; mul to _*_)
