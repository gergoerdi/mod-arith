module Data.Mod where

module Dummy where
  open import Data.Nat using (ℕ)
  open import Data.Integer
  open import Data.Nat.Divisibility
  open import Quotient -- http://www.cs.nott.ac.uk/~txa/AIMXV/Quotient.html/Quotient.html
  open import Function using (_∘_; _⟨_⟩_)

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open ≡-Reasoning

  open import Algebra
  import Data.Integer.Properties as Integer
  open CommutativeRing Integer.commutativeRing using (-‿inverse; 1#; 0#)
  open import Data.Product

  open import Data.Mod.Lemmas

  private
    Mod₀ : ℕ → Setoid _ _
    Mod₀ n = record
      { Carrier = ℤ
      ; _≈_ = _∼_
      ; isEquivalence = record
        { refl = λ {x} → reflexive {x}
        ; sym = λ {x} {y} → symmetric {x} {y}
        ; trans = λ {x} {y} {z} → transitive {x} {y} {z}
        }
      }

      where
        _∼_ : Rel ℤ _
        x ∼ y = n ∣ ∣ x - y ∣

        reflexive : Reflexive _∼_
        reflexive {x} = divides 0 (cong ∣_∣ (proj₂ -‿inverse x))

        symmetric : Symmetric _∼_
        symmetric {x} {y} (divides q eq) = divides q (abs-flip y x ⟨ trans ⟩ eq)

        transitive : Transitive _∼_
        transitive {x} {y} {z} d d′ = subst (_∣_ n) (cong ∣_∣ (telescope x y z)) (∣-abs-+ (x - y) (y - z) d d′)

  Mod : ℕ → Set
  Mod n = Quotient (Mod₀ n)

  open import Quotient.Op
  open Integer.RingSolver

  plus : ∀ {n} → Mod n → Mod n → Mod n
  plus {n} = lift₂ _+_ (λ {x} {y} {t} {u} → proof {x} {y} {t} {u})
    where
    proof : ∀ {x y t u} → (n ∣ ∣ x - y ∣) → (n ∣ ∣ t - u ∣) → n ∣ ∣ (x + t) - (y + u) ∣
    proof {x} {y} {t} {u} x∼y t∼u = subst ((_∣_ n) ∘ ∣_∣) (sym (eq x y t u)) (∣-abs-+ (x - y) (t - u) x∼y t∼u)
      where
      eq : _
      eq = solve 4 (λ a b c d → (a :+ c) :- (b :+ d) := (a :- b) :+ (c :- d)) refl

  minus : ∀ {n} → Mod n → Mod n → Mod n
  minus {n} = lift₂ _-_ (λ {x} {y} {t} {u} → proof {x} {y} {t} {u})
    where
    proof : ∀ {x y t u} → (n ∣ ∣ x - y ∣) → (n ∣ ∣ t - u ∣) → n ∣ ∣ (x - t) - (y - u) ∣
    proof {x} {y} {t} {u} x∼y t∼u = subst ((_∣_ n) ∘ ∣_∣) (sym (eq x y t u)) (∣-abs‿- (x + - y) (t + - u) x∼y t∼u)
      where
      eq : _
      eq = solve 4 (λ a b c d → (a :- c) :- (b :- d) := (a :- b) :- (c :- d)) refl

  -- Derived operations
  _+1 : ∀ {n} → Mod n → Mod n
  _+1 x = x ⟨ plus ⟩ [ 1# ]

  _-1 : ∀ {n} → Mod n → Mod n
  _-1 x = x ⟨ minus ⟩ [ 1# ]

  +1-1 : ∀ {n} → (x : Mod n) → x +1 -1 ≡ x
  +1-1 {n} = elim _ (λ x → [ proof x ]-cong) (λ x∼y → proof-irrelevance _ _)
    where
    proof : ∀ x → n ∣ ∣ (x + (+ 1) - (+ 1)) - x ∣
    proof = divides 0 ∘ cong ∣_∣ ∘ solve 1 (λ x → x :+ con 1# :- con 1# :- x := con 0#) refl

open Dummy public renaming (plus to _+_; minus to _-_)
