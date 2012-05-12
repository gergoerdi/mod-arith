module Data.Mod where

open import Data.Integer using (ℤ)

private
  open import Data.Nat using (ℕ; zero; suc; _≤?_; _≥_)

  open import Algebra
  import Data.Nat.Properties
  module ℕ-CS = CommutativeSemiring Data.Nat.Properties.commutativeSemiring
  import Data.Integer.Properties
  module ℤ-CR = CommutativeRing Data.Integer.Properties.commutativeRing
  open import Relation.Nullary.Decidable

  module Dummy (n : ℕ) {≥2 : True (2 ≤? n)} where
    open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

    private
      module Divisor-Props where
        open import Data.Nat
        open import Data.Empty
        open import Relation.Binary
        open import Relation.Nullary
        open import Function

        n≥2 : n ≥ 2
        n≥2 = toWitness ≥2

        fromWitnessFalse : ∀ {p} {P : Set p} {Q : Dec P} → ¬ P → False Q
        fromWitnessFalse {Q = yes p} = flip _$_ p
        fromWitnessFalse {Q = no ¬p} = const _

        n≢0 : False (n ≟ 0)
        n≢0 = fromWitnessFalse (≥2⇒≢0 n≥2)
          where
          open import Data.Nat.Properties

          ≥2⇒≢0 : ∀ {k} → k ≥ 2 → k ≢ 0
          ≥2⇒≢0 {.(suc k)} (s≤s {.1} {k} m≤n) = i+1+j≢i zero

      open Divisor-Props

      module Neg-Fin where
        private
          open import Data.Nat
          open import Data.Fin hiding (_≤_; _+_)
          open import Data.Fin.Props
          open import Data.Nat.Properties
          open import Function

          toℕ-cancel : ∀ {k} → {i j : Fin k} → toℕ i ≡ toℕ j → i ≡ j
          toℕ-cancel {i = zero} {j = zero} i′≡j′ = P.refl
          toℕ-cancel {i = zero} {j = suc i} ()
          toℕ-cancel {i = suc i} {j = zero} ()
          toℕ-cancel {i = suc i} {j = suc j} i′≡j′ = P.cong suc (toℕ-cancel (cancel-+-left 1 i′≡j′))

        reverse-neg : ∀ {k} → (i : Fin k) → toℕ (reverse i) ≡ k ∸ suc (toℕ i)
        reverse-neg {zero} ()
        reverse-neg {suc k} i = inject≤-lemma _ _ ⟨ P.trans ⟩ toℕ‿ℕ- k i
          where
          toℕ‿ℕ- : ∀ k i → toℕ (k ℕ- i) ≡ k ∸ toℕ i
          toℕ‿ℕ- k zero = to-from k
          toℕ‿ℕ- zero (suc ())
          toℕ‿ℕ- (suc k) (suc i) = toℕ‿ℕ- k i

        reverse-inv : ∀ {k} → (i : Fin k) → reverse (reverse i) ≡ i
        reverse-inv {k} i = toℕ-cancel (reverse-neg _ ⟨ P.trans ⟩ eq)
          where
          open P.≡-Reasoning
          open import Algebra

          lem₁ : ∀ m n → (m + n) ∸ (m + n ∸ m) ≡ m
          lem₁ m n =
            begin
              m + n ∸ (m + n ∸ m)
            ≡⟨ P.cong (λ ξ → m + n ∸ (ξ ∸ m)) (ℕ-CS.+-comm m n) ⟩
              m + n ∸ (n + m ∸ m)
            ≡⟨ P.cong (λ ξ → m + n ∸ ξ) (m+n∸n≡m n m) ⟩
              m + n ∸ n
            ≡⟨ m+n∸n≡m m n ⟩
              m
            ∎

          lem₂ : ∀ k → (i : Fin k) → k ∸ suc (k ∸ suc (toℕ i)) ≡ toℕ i
          lem₂ zero ()
          lem₂ (suc k) i =
            begin
              k ∸ (k ∸ toℕ i)
            ≡⟨ P.cong (λ ξ → ξ ∸ (ξ ∸ toℕ i)) i+j≡k ⟩
              (toℕ i + j) ∸ (toℕ i + j ∸ toℕ i)
            ≡⟨ lem₁ (toℕ i) j ⟩
              toℕ i
            ∎
            where
            open import Data.Product

            decompose-k : ∃ λ j → k ≡ toℕ i + j
            decompose-k = k ∸ toℕ i , P.sym (m+n∸m≡n (prop-toℕ-≤ i))

            j = proj₁ decompose-k
            i+j≡k = proj₂ decompose-k

          eq : k ∸ suc (toℕ (reverse i)) ≡ toℕ i
          eq =
            begin
              k ∸ suc (toℕ (reverse i))
            ≡⟨ P.cong (λ ξ → k ∸ suc ξ) (reverse-neg i) ⟩
              k ∸ suc (k ∸ suc (toℕ i))
            ≡⟨ lem₂ k i ⟩
              toℕ i
            ∎

    open import Data.Integer hiding (suc)
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

    open import Algebra.FunctionProperties using (Op₁; Op₂)
    open Setoid Mod

    open import Data.Fin using (Fin)
    open import Data.Fin.Props using (reverse)
    open import Data.Nat.DivMod

    normalize : Carrier → Fin n
    normalize (+ x) = (x mod n) {n≢0}
    normalize -[1+ x ] = reverse ((x mod n) {n≢0})

    abstract
      open import Data.Fin using (toℕ)
      open import Data.Nat renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)

      normalize-correct : ∀ x → x ∼ (+ (toℕ (normalize x)))
      normalize-correct -[1+ x ] with (x divMod n) {n≢0}
      normalize-correct -[1+ .(toℕ r ℕ+ q ℕ* n) ] | result q r = divides (suc q) eq′
        where
        x′ : ℕ
        x′ = toℕ r ℕ+ q ℕ* n

        open P.≡-Reasoning
        open Data.Nat.Properties

        lem : ∀ x y → - (x - y) ≡ y - x
        lem -[1+ zero ] -[1+ zero ] = P.refl
        lem -[1+ suc _ ] -[1+ zero ] = P.refl
        lem (+ zero) -[1+ zero ] = P.refl
        lem (+ suc x) -[1+ zero ] = P.cong -[1+_] (ℕ-CS.+-comm x _)
        lem -[1+ zero ] -[1+ suc _ ] = P.refl
        lem -[1+ suc x ] -[1+ suc y ] = lem -[1+ x ] -[1+ y ]
        lem (+ zero) -[1+ suc y ] = P.refl
        lem (+ suc x) -[1+ suc y ] = P.cong -[1+_] (ℕ-CS.+-comm x _)
        lem -[1+ zero ] (+ zero) = P.refl
        lem -[1+ zero ] (+ suc y) = P.cong +_ (ℕ-CS.+-comm (suc zero) _)
        lem -[1+ suc x ] (+ zero) = P.refl
        lem -[1+ suc x ] (+ suc y) = P.cong (+_ ∘ suc) (ℕ-CS.+-comm _ y)
        lem (+ zero) (+ zero) = P.refl
        lem (+ zero) (+ suc y) = P.cong (+_ ∘ suc) (ℕ-CS.+-comm _ y)
        lem (+ suc x) (+ zero) = P.cong -[1+_] (proj₂ ℕ-CS.+-identity x)
        lem (+ suc x) (+ suc y) = lem -[1+ y ] -[1+ x ]

        eq′ : ∣ -[1+ x′ ] - (+ toℕ (reverse r))  ∣ ≡ suc q ℕ* n
        eq′ =
          begin
            ∣ -[1+ x′ ] - (+ toℕ (reverse r)) ∣
          ≡⟨ P.sym (abs-neg (-[1+ x′ ] + - (+ toℕ (reverse r)))) ⟩
            ∣ - (-[1+ x′ ] - (+ toℕ (reverse r))) ∣
          ≡⟨ P.cong ∣_∣ (lem -[1+ x′ ] (+ toℕ (reverse r))) ⟩
            toℕ (reverse r) ℕ+ (suc x′)
          ≡⟨ P.cong (λ ξ → ξ ℕ+ (suc x′)) (Neg-Fin.reverse-neg r) ⟩
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
          open import Data.Fin.Props

          r<n : toℕ r < n
          r<n = prop-toℕ-≤ (Data.Fin.suc r)

      normalize-correct (+ x) with (x divMod n) {n≢0}
      normalize-correct (+ .(toℕ r ℕ+ q ℕ* n)) | result q r = divides q eq
        where
        open P.≡-Reasoning

        eq : ∣ + (toℕ r ℕ+ q ℕ* n) - (+ toℕ r) ∣ ≡ q ℕ* n
        eq =
          begin
            ∣ + (toℕ r ℕ+ q ℕ* n) - (+ toℕ r) ∣
          ≡⟨ P.refl ⟩
            ∣ (+ toℕ r) + (+ (q ℕ* n)) - (+ toℕ r) ∣
          ≡⟨ P.cong (λ ξ → ∣ ξ - + toℕ r ∣) (ℤ-CR.+-comm (+ toℕ r) (+ (q ℕ* n))) ⟩
            ∣ (+ (q ℕ* n)) + (+ toℕ r) - (+ toℕ r) ∣
          ≡⟨ P.cong ∣_∣ (ℤ-CR.+-assoc (+ (q ℕ* n)) (+ toℕ r) (- (+ toℕ r))) ⟩
            ∣ (+ (q ℕ* n)) + ((+ toℕ r) - (+ toℕ r)) ∣
          ≡⟨ P.cong (λ ξ → ∣ (+ (q ℕ* n)) + ξ ∣) (proj₂ ℤ-CR.-‿inverse (+ toℕ r)) ⟩
            ∣ (+ (q ℕ* n)) + (+ 0) ∣
          ≡⟨ P.cong ∣_∣ (proj₂ ℤ-CR.+-identity (+ (q ℕ* n))) ⟩
            ∣ + (q ℕ* n) ∣
          ≡⟨ P.refl ⟩
            q ℕ* n
          ∎

    plus : Op₂ Carrier
    plus = _+_

    neg : Op₁ Carrier
    neg = -_

    minus : Op₂ Carrier
    minus = _-_

    mul : Op₂ Carrier
    mul = _*_

    private
      Sound₁ : Op₁ Carrier → Set
      Sound₁ f = f Preserves _∼_ ⟶ _∼_

      Sound₂ : Op₂ Carrier → Set
      Sound₂ ∙ = ∙ Preserves₂ _∼_ ⟶ _∼_ ⟶ _∼_

      abstract
        open Integer.RingSolver

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
      private
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

      commutativeRing : CommutativeRing _ _
      commutativeRing = record
        { Carrier           = ℤ
        ; _≈_               = _∼_
        ; _+_               = plus
        ; _*_               = mul
        ; -_                = neg
        ; 0#                = + 0
        ; 1#                = + 1
        ; isCommutativeRing = isCommutativeRing
        }

      import Algebra.RingSolver.Simple as Solver
      import Algebra.RingSolver.AlmostCommutativeRing as ACR
      module RingSolver = Solver (ACR.fromCommutativeRing commutativeRing)

open Dummy public using (module Properties)

[_] : ℕ → ℤ
[ n ] = + n

