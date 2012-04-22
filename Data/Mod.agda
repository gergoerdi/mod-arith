module Data.Mod where

open import Data.Nat using (ℕ)

module Dummy {n : ℕ} where
  open import Data.Integer
  open import Data.Nat.Divisibility
  open import Quotient
  open import Function using (_∘_; _⟨_⟩_)
  import Level

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as P using (_≡_)
  open P.≡-Reasoning

  open import Algebra
  import Data.Integer.Properties as Integer
  open CommutativeRing Integer.commutativeRing using (-‿inverse; 1#; 0#)
  open import Data.Product

  open import Data.Mod.Lemmas

  private
    Mod₀ : Setoid Level.zero Level.zero
    Mod₀ = record
      { Carrier = ℤ
      ; _≈_ = _∼_
      ; isEquivalence = isEquivalence
      }

      where
        _∼_ : Rel ℤ _
        x ∼ y = n ∣ ∣ x - y ∣

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


  Mod : Set
  Mod = Quotient Mod₀

  import Quotient.Op
  open Quotient.Op Mod₀
  open Integer.RingSolver
  open import Algebra.FunctionProperties using (Op₁; Op₂)

  plus₀ : LiftOp₂
  plus₀ = _+_ , λ {x y t u} → proof x y t u
    where
    abstract
      proof : ∀ x y t u → (n ∣ ∣ x - y ∣) → (n ∣ ∣ t - u ∣) → n ∣ ∣ (x + t) - (y + u) ∣
      proof x y t u x∼y t∼u = P.subst ((_∣_ n) ∘ ∣_∣) (P.sym (eq x y t u)) (∣-abs-+ (x - y) (t - u) x∼y t∼u)
        where
        eq : ∀ a b c d → (a + c) - (b + d) ≡ (a - b) + (c - d)
        eq = solve 4 (λ a b c d → (a :+ c) :- (b :+ d) := (a :- b) :+ (c :- d)) P.refl

  plus : Op₂ Mod
  plus = lift₂ plus₀

  minus₀ : LiftOp₂
  minus₀ = _-_ , λ {x y t u} → proof x y t u
    where
    abstract
      proof : ∀ x y t u → (n ∣ ∣ x - y ∣) → (n ∣ ∣ t - u ∣) → n ∣ ∣ (x - t) - (y - u) ∣
      proof x y t u x∼y t∼u = P.subst ((_∣_ n) ∘ ∣_∣) (P.sym (eq x y t u)) (∣-abs‿- (x + - y) (t + - u) x∼y t∼u)
        where
        eq : ∀ a b c d → (a - c) - (b - d) ≡ (a - b) - (c - d)
        eq = solve 4 (λ a b c d → (a :- c) :- (b :- d) := (a :- b) :- (c :- d)) P.refl

  minus : Op₂ Mod
  minus = lift₂ minus₀

  -- Derived operations
  _+1 : Op₁ Mod
  _+1 x = x ⟨ plus ⟩ [ 1# ]

  _-1 : Op₁ Mod
  _-1 x = x ⟨ minus ⟩ [ 1# ]

  +1-1 : (x : Mod) → x +1 -1 ≡ x
  +1-1 = elim _ _ (λ x → [ proof x ]-cong) (λ x∼y → P.proof-irrelevance _ _)
    where
    abstract
      proof : ∀ x → n ∣ ∣ (x + (+ 1) - (+ 1)) - x ∣
      proof = divides 0 ∘ P.cong ∣_∣ ∘ solve 1 (λ x → x :+ con 1# :- con 1# :- x := con 0#) P.refl

  module Properties where
    import Algebra.FunctionProperties as FunProp
    open FunProp (_≡_ {A = Mod})

    import Data.Integer.Properties as Integer
    private
      module ℤ-CR = CommutativeRing Integer.commutativeRing

    plus-assoc : Associative plus
    plus-assoc = lift-assoc′ plus₀ ℤ-CR.+-assoc

    plus-comm : Commutative plus
    plus-comm = lift-comm′ plus₀ ℤ-CR.+-comm

    open import Algebra.Structures

    isSemigroup : IsSemigroup _≡_ plus
    isSemigroup = record
      { isEquivalence = isEquivalence
      ; assoc = plus-assoc
      ; ∙-cong = cong₂ plus
      }
      where
      open import Relation.Binary.PropositionalEquality

open Dummy public renaming (plus to _+_; minus to _-_)
