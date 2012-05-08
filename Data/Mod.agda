module Data.Mod where

private
  open import Data.Nat using (ℕ) renaming (_*_ to _ℕ*_)

  module Dummy (n : ℕ) where
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

      Sound₁ : Op₁ Carrier → Set
      Sound₁ f = f Preserves _∼_ ⟶ _∼_

      Sound₂ : Op₂ Carrier → Set
      Sound₂ ∙ = ∙ Preserves₂ _∼_ ⟶ _∼_ ⟶ _∼_

    open Integer.RingSolver

    plus : Op₂ Carrier
    plus = _+_

    neg : Op₁ Carrier
    neg = -_

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

      neg-sound : Sound₁ neg
      neg-sound {x} {x′} x∼x′ = ∣-abs-neg x x′ x∼x′

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

      plus-isAbelianGroup : IsAbelianGroup _∼_ plus (+ 0) neg
      plus-isAbelianGroup = record
        { isGroup = isGroup
        ; comm = plus-comm
        }
        where
        abstract
          module S = Setoid Mod

          inverseˡ : LeftInverse (+ 0) neg plus
          inverseˡ x = P.subst (_∣_ n) (P.cong ∣_∣ (solve 1 (λ ξ → (con (+ 0) := (:- ξ :+ ξ :+ con (+ 0)))) P.refl x)) (n ∣0)

          inverseʳ : RightInverse (+ 0) neg plus
          inverseʳ x = P.subst (_∣_ n) (P.cong ∣_∣ (solve 1 (λ ξ → (con (+ 0) := (ξ :- ξ :+ con (+ 0)))) P.refl x)) (n ∣0)

          plus-identityˡ : LeftIdentity (+ 0) plus
          plus-identityˡ = λ x → S.reflexive (proj₁ ℤ-CR.+-identity x)

          plus-identityʳ : RightIdentity (+ 0) plus
          plus-identityʳ = λ x → S.reflexive (proj₂ ℤ-CR.+-identity x)

          plus-comm : Commutative plus
          plus-comm = λ x y → S.reflexive (ℤ-CR.+-comm x y)

          isMonoid : IsMonoid _∼_ plus (+ 0)
          isMonoid = record
            { isSemigroup = record
              { isEquivalence = isEquivalence
              ; assoc = λ x y z → S.reflexive (ℤ-CR.+-assoc x y z)
              ; ∙-cong = λ {x} {x′} {y} {y′} x∼x′ y∼y′ → plus-sound {x} {x′} {y} {y′} x∼x′ y∼y′
              }
            ; identity = plus-identityˡ , plus-identityʳ
            }

          isGroup : IsGroup _∼_ plus (+ 0) neg
          isGroup = record
            { isMonoid = isMonoid
            ; inverse = inverseˡ , inverseʳ
            ; ⁻¹-cong = λ {x x′} x∼y → neg-sound {x} {x′} x∼y
            }

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

      isCommutativeRing : IsCommutativeRing _∼_ plus mul neg (+ 0) (+ 1)
      isCommutativeRing = record
        { isRing = isRing
        ; *-comm = mul-comm
        }
        where
        abstract
          module S = Setoid Mod

          isRing : IsRing _∼_ plus mul neg (+ 0) (+ 1)
          isRing = record
            { +-isAbelianGroup = plus-isAbelianGroup
            ; *-isMonoid = mul-isMonoid
            ; distrib = distrib
            }
            where

            distribˡ : mul DistributesOverˡ plus
            distribˡ = λ x y z → S.reflexive (proj₁ ℤ-CR.distrib x y z)

            distribʳ : mul DistributesOverʳ plus
            distribʳ = λ x y z → S.reflexive (proj₂ ℤ-CR.distrib x y z)

            distrib : mul DistributesOver plus
            distrib = distribˡ , distribʳ

          mul-comm : Commutative mul
          mul-comm = λ x y → S.reflexive (ℤ-CR.*-comm x y)

open Dummy public renaming (plus to _+_; minus to _-_; mul to _*_)
