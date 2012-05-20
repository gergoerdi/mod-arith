module Data.Mod.Properties where

import Data.Mod

private
  open import Data.Nat using (ℕ; zero; suc; _≤?_; _≥_)

  open import Relation.Nullary.Decidable

  module Dummy (n : ℕ) {≥2 : True (2 ≤? n)} where

    -- open Data.Mod n {≥2}

    open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

    private
      module Fin-Reverse-Props where
        open import Data.Fin
        open import Data.Fin.Props
        open import Data.Nat renaming (_+_ to _ℕ+_)
        open import Function

        reverse-prop : ∀ {n} → (i : Fin n) → toℕ (reverse i) ≡ n ∸ suc (toℕ i)
        reverse-prop {zero} ()
        reverse-prop {suc n} i = inject≤-lemma _ _ ⟨ P.trans ⟩ toℕ‿ℕ- n i
          where
          toℕ‿ℕ- : ∀ n i → toℕ (n ℕ- i) ≡ n ∸ toℕ i
          toℕ‿ℕ- n zero = to-from n
          toℕ‿ℕ- zero (suc ())
          toℕ‿ℕ- (suc n) (suc i) = toℕ‿ℕ- n i

        open import Algebra.FunctionProperties

        reverse-involutive : ∀ {n} → Involutive _≡_ reverse
        reverse-involutive {n} i = toℕ-injective (reverse-prop _ ⟨ P.trans ⟩ eq)
          where
          open P.≡-Reasoning
          open import Algebra
          import Data.Nat.Properties as N
          open CommutativeSemiring N.commutativeSemiring using (+-comm)

          lem₁ : ∀ m n → (m ℕ+ n) ∸ (m ℕ+ n ∸ m) ≡ m
          lem₁ m n = begin
            m ℕ+ n ∸ (m ℕ+ n ∸ m) ≡⟨ P.cong (λ ξ → m ℕ+ n ∸ (ξ ∸ m)) (+-comm m n) ⟩
            m ℕ+ n ∸ (n ℕ+ m ∸ m) ≡⟨ P.cong (λ ξ → m ℕ+ n ∸ ξ) (N.m+n∸n≡m n m) ⟩
            m ℕ+ n ∸ n            ≡⟨ N.m+n∸n≡m m n ⟩
            m                     ∎

          lem₂ : ∀ n → (i : Fin n) → n ∸ suc (n ∸ suc (toℕ i)) ≡ toℕ i
          lem₂ zero ()
          lem₂ (suc n) i = begin
            n ∸ (n ∸ toℕ i)                     ≡⟨ P.cong (λ ξ → ξ ∸ (ξ ∸ toℕ i)) i+j≡k ⟩
            (toℕ i ℕ+ j) ∸ (toℕ i ℕ+ j ∸ toℕ i) ≡⟨ lem₁ (toℕ i) j ⟩
            toℕ i                               ∎
            where
            open import Data.Product

            decompose-n : ∃ λ j → n ≡ toℕ i ℕ+ j
            decompose-n = n ∸ toℕ i , P.sym (N.m+n∸m≡n (prop-toℕ-≤ i))

            j = proj₁ decompose-n
            i+j≡k = proj₂ decompose-n

          eq : n ∸ suc (toℕ (reverse i)) ≡ toℕ i
          eq = begin
            n ∸ suc (toℕ (reverse i)) ≡⟨ P.cong (λ ξ → n ∸ suc ξ) (reverse-prop i) ⟩
            n ∸ suc (n ∸ suc (toℕ i)) ≡⟨ lem₂ n i ⟩
            toℕ i                     ∎

      open Fin-Reverse-Props

      module Divisor-Props where
        open import Data.Nat
        open import Data.Empty
        open import Relation.Binary
        open import Relation.Nullary
        open import Function

        n≥2 : n ≥ 2
        n≥2 = toWitness ≥2

        n≢0 : False (n ≟ 0)
        n≢0 = fromWitnessFalse (≥2⇒≢0 n≥2)
          where
          open import Data.Nat.Properties

          ≥2⇒≢0 : ∀ {k} → k ≥ 2 → k ≢ 0
          ≥2⇒≢0 {.(suc k)} (s≤s {.1} {k} m≤n) = i+1+j≢i zero

      open Divisor-Props

      open import Relation.Binary
      open import Algebra
      import Data.Nat.Properties as Nat
      module ℕ-CS = CommutativeSemiring Nat.commutativeSemiring
      import Data.Integer.Properties as Integer
      module ℤ-CR = CommutativeRing Integer.commutativeRing

      module Normalise where
        open Data.Mod n {≥2} using (Mod)

        open import Data.Integer hiding (suc)
        open import Data.Nat.Divisibility hiding (*-cong)
        open import Function using (_∘_; _⟨_⟩_)

        open import Data.Product

        open import Data.Mod.Lemmas

        open Setoid Mod

        open import Data.Fin using (Fin; toℕ)
        open import Data.Fin.Props
        open import Data.Nat.DivMod

        normalise₀ : Carrier → Fin n
        normalise₀ (+ x) = (x mod n) {n≢0}
        normalise₀ -[1+ x ] = reverse ((x mod n) {n≢0})

        normalise : Carrier → Carrier
        normalise = +_ ∘ toℕ ∘ normalise₀

        open import Data.Nat renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)

        normalise-correct : ∀ x → normalise x ≈ x
        normalise-correct -[1+ x ] with (x divMod n) {n≢0}
        normalise-correct -[1+ .(toℕ r ℕ+ q ℕ* n) ] | result q r = divides (suc q) eq
          where
          x′ : ℕ
          x′ = toℕ r ℕ+ q ℕ* n

          open P.≡-Reasoning
          open Nat

          lem : ∀ x y → - (x - y) ≡ y - x
          lem = solve 2 (λ x y → :- (x :- y) := y :- x) P.refl
            where
            open Integer.RingSolver

          eq : toℕ (reverse r) ℕ+ suc x′ ≡ suc q ℕ* n
          eq =
            begin
              toℕ (reverse r) ℕ+ (suc x′)
            ≡⟨ P.cong (λ ξ → ξ ℕ+ (suc x′)) (reverse-prop r) ⟩
              (n ∸ suc (toℕ r)) ℕ+ (suc x′)
            ≡⟨ P.cong (λ ξ → (n ∸ suc (toℕ r)) ℕ+ suc ξ) P.refl ⟩
              (n ∸ suc (toℕ r)) ℕ+ (suc (toℕ r) ℕ+ q ℕ* n)
            ≡⟨ P.sym (ℕ-CS.+-assoc (n ∸ suc (toℕ r)) (suc (toℕ r)) (q ℕ* n)) ⟩
              (n ∸ suc (toℕ r) ℕ+ suc (toℕ r)) ℕ+ (q ℕ* n)
            ≡⟨ P.cong (λ ξ → ξ ℕ+ q ℕ* n) (ℕ-CS.+-comm (n ∸ suc (toℕ r)) (suc (toℕ r))) ⟩
              (suc (toℕ r) ℕ+ (n ∸ suc (toℕ r))) ℕ+ (q ℕ* n)
            ≡⟨ P.cong (λ ξ → ξ ℕ+ q ℕ* n) (m+n∸m≡n r<n) ⟩
              suc q ℕ* n
            ∎
            where
            r<n : toℕ r < n
            r<n = prop-toℕ-≤ (Data.Fin.suc r)
        normalise-correct (+ x) with (x divMod n) {n≢0}
        normalise-correct (+ .(toℕ r ℕ+ q ℕ* n)) | result q r = divides q eq
          where
          open P.≡-Reasoning

          lem₁ : ∀ x y → x - y ≡ - (y - x)
          lem₁ = solve 2 (λ x y → x :- y := :- (y :- x)) P.refl
            where
            open Integer.RingSolver

          lem₂ : ∀ x y → x + y - x ≡ y
          lem₂ x y =
            begin
              x + y - x
            ≡⟨ P.cong (λ ξ → ξ - x) (ℤ-CR.+-comm x y) ⟩
              y + x - x
            ≡⟨ ℤ-CR.+-assoc y x (- x) ⟩
              y + (x - x)
            ≡⟨ P.cong (_+_ y) (proj₂ ℤ-CR.-‿inverse x) ⟩
              y + (+ 0)
            ≡⟨ proj₂ ℤ-CR.+-identity y ⟩
              y
            ∎

          eq : ∣ (+ toℕ r) - (+ (toℕ r ℕ+ q ℕ* n)) ∣ ≡ q ℕ* n
          eq =
            begin
              ∣ + toℕ r - + (toℕ r ℕ+ q ℕ* n) ∣
            ≡⟨ P.cong ∣_∣ (lem₁ (+ toℕ r) (+ (toℕ r ℕ+ q ℕ* n))) ⟩
              ∣ - (+ (toℕ r ℕ+ q ℕ* n) - (+ toℕ r)) ∣
            ≡⟨ abs-neg (+ (toℕ r ℕ+ q ℕ* n) + - (+ toℕ r)) ⟩
              ∣ + (toℕ r ℕ+ q ℕ* n) - (+ toℕ r) ∣
            ≡⟨ P.refl ⟩
              ∣ (+ toℕ r) + (+ (q ℕ* n)) - (+ toℕ r) ∣
            ≡⟨ P.cong ∣_∣ (lem₂ (+ toℕ r) (+ (q ℕ* n))) ⟩
              ∣ + (q ℕ* n) ∣
            ≡⟨ P.refl ⟩
              q ℕ* n
            ∎
            where
            open Integer.RingSolver

        normalise-correct-sym : ∀ x → x ≈ normalise x
        normalise-correct-sym x = sym {+ toℕ (normalise₀ x)} {x} (normalise-correct x)

      module Structure where
        open Data.Mod n {≥2}
        open Setoid Mod

        import Algebra.FunctionProperties as FunProp
        open FunProp (_≈_)

        open import Data.Integer using (∣_∣)
        import Data.Integer.Properties as Integer
        open import Data.Nat.Divisibility hiding (*-cong)
        open import Data.Product

        open import Algebra.Structures

        plus-isAbelianGroup : IsAbelianGroup _≈_ _+_ [ 0 ] -_
        plus-isAbelianGroup = record
          { isGroup = isGroup
          ; comm = plus-comm
          }
          where
          abstract
            open Integer.RingSolver

            inverseˡ : LeftInverse [ 0 ] -_ _+_
            inverseˡ x = P.subst (_∣_ n) (P.cong ∣_∣ (solve 1 (λ ξ → (con [ 0 ] := (:- ξ :+ ξ :+ con [ 0 ]))) P.refl x)) (n ∣0)

            inverseʳ : RightInverse [ 0 ] -_ _+_
            inverseʳ x = P.subst (_∣_ n) (P.cong ∣_∣ (solve 1 (λ ξ → (con [ 0 ] := (ξ :- ξ :+ con [ 0 ]))) P.refl x)) (n ∣0)

            plus-identityˡ : LeftIdentity [ 0 ] _+_
            plus-identityˡ = λ x → reflexive (proj₁ ℤ-CR.+-identity x)

            plus-identityʳ : RightIdentity [ 0 ] _+_
            plus-identityʳ = λ x → reflexive (proj₂ ℤ-CR.+-identity x)

            plus-comm : Commutative _+_
            plus-comm = λ x y → reflexive (ℤ-CR.+-comm x y)

            isMonoid : IsMonoid _≈_ _+_ [ 0 ]
            isMonoid = record
              { isSemigroup = record
                { isEquivalence = isEquivalence
                ; assoc = λ x y z → reflexive (ℤ-CR.+-assoc x y z)
                ; ∙-cong = λ {x} {x′} {y} {y′} x∼x′ y∼y′ → plus-sound {x} {x′} {y} {y′} x∼x′ y∼y′
                }
              ; identity = plus-identityˡ , plus-identityʳ
              }

            isGroup : IsGroup _≈_ _+_ [ 0 ] -_
            isGroup = record
              { isMonoid = isMonoid
              ; inverse = inverseˡ , inverseʳ
              ; ⁻¹-cong = λ {x x′} x∼y → neg-sound {x} {x′} x∼y
              }

        mul-isMonoid : IsMonoid _≈_ _*_ [ 1 ]
        mul-isMonoid = record
          { isSemigroup = isSemigroup
          ; identity = mul-identityˡ , mul-identityʳ
          }
          where
          abstract
            isSemigroup : IsSemigroup _≈_ _*_
            isSemigroup = record
              { isEquivalence = isEquivalence
              ; assoc = λ x y z → reflexive (ℤ-CR.*-assoc x y z)
              ; ∙-cong = λ {x x′ y y′} x∼x′ y∼y′ → mul-sound {x} {x′} {y} {y′} x∼x′ y∼y′
              }

            mul-identityˡ : LeftIdentity [ 1 ] _*_
            mul-identityˡ = λ x → reflexive (proj₁ ℤ-CR.*-identity x)

            mul-identityʳ : RightIdentity [ 1 ] _*_
            mul-identityʳ = λ x → reflexive (proj₂ ℤ-CR.*-identity x)

        isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ [ 0 ] [ 1 ]
        isCommutativeRing = record
          { isRing = isRing
          ; *-comm = mul-comm
          }
          where
          abstract
            module S = Setoid Mod

            isRing : IsRing _≈_ _+_ _*_ -_ [ 0 ] [ 1 ]
            isRing = record
              { +-isAbelianGroup = plus-isAbelianGroup
              ; *-isMonoid = mul-isMonoid
              ; distrib = distrib
              }
              where

              distribˡ : _*_ DistributesOverˡ _+_
              distribˡ = λ x y z → S.reflexive (proj₁ ℤ-CR.distrib x y z)

              distribʳ : _*_ DistributesOverʳ _+_
              distribʳ = λ x y z → S.reflexive (proj₂ ℤ-CR.distrib x y z)

              distrib : _*_ DistributesOver _+_
              distrib = distribˡ , distribʳ

            mul-comm : Commutative _*_
            mul-comm = λ x y → S.reflexive (ℤ-CR.*-comm x y)

        commutativeRing : CommutativeRing _ _
        commutativeRing = record
          { Carrier           = _
          ; _≈_               = _
          ; _+_               = _
          ; _*_               = _
          ; -_                = _
          ; 0#                = _
          ; 1#                = _
          ; isCommutativeRing = isCommutativeRing
          }

        private
          open Normalise

          open import Algebra.RingSolver.AlmostCommutativeRing as ACR
          R₀ = ACR.fromCommutativeRing commutativeRing
          module R = AlmostCommutativeRing R₀

          normalised-ring : R.rawRing -Raw-AlmostCommutative⟶ R₀
          normalised-ring = record
            { ⟦_⟧ = normalise
            ; +-homo = {!!} -- λ x y → normalise-correct x ⟨ +-cong ⟩ normalise-correct y
            ; *-homo = {!!} -- λ x y → normalise-correct x ⟨ *-cong ⟩ normalise-correct y
            ; -‿homo = λ x →
              begin
                normalise (- x)
              ≈⟨ normalise-correct (- x) ⟩
                - x
              ≈⟨ -‿cong {x} (normalise-correct-sym x) ⟩
                - (normalise x)
              ∎
            ; 0-homo = normalise-correct [ 0 ]
            ; 1-homo = normalise-correct [ 1 ]
            }
            where
            module S = Setoid Mod
            import Relation.Binary.EqReasoning
            open Relation.Binary.EqReasoning Mod
            module CR = CommutativeRing commutativeRing
            open CR hiding (-_) -- TODO

        import Algebra.RingSolver
        module Solver = Algebra.RingSolver R.rawRing R₀ normalised-ring

