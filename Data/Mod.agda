module Data.Mod where

open import Data.Nat renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties
open import Data.Integer hiding (_*_; _≤_) renaming (suc to ℤsuc; pred to ℤpred)
open import Data.Integer.Properties
open import Data.Nat.Divisibility
open import Quotient -- http://www.cs.nott.ac.uk/~txa/AIMXV/Quotient.html/Quotient.html
open import Function using (_∘_; const)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open ≡-Reasoning

open import Algebra
import Data.Nat.Properties as Nat
private
  module ℕ-CS = CommutativeSemiring Nat.commutativeSemiring
import Data.Integer.Properties as Integer
private
  module ℤ-CR = CommutativeRing Integer.commutativeRing
private
  module ℕ-Ord = StrictTotalOrder Nat.strictTotalOrder
open import Data.Product

private
  open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; refl; sym; cong; cong₂)
  open PropEq.≡-Reasoning

  neg-minus-pos : (x y : ℕ) → -[1+ x ] - (+ y) ≡ -[1+ (y ℕ+ x) ]
  neg-minus-pos x zero = refl
  neg-minus-pos zero (suc y) = cong (-[1+_] ∘ suc) (sym (proj₂ ℕ-CS.+-identity y))
  neg-minus-pos (suc x) (suc y) = cong (-[1+_] ∘ suc) (ℕ-CS.+-comm (suc x) y)

  flip-suc : ∀ x y → x ℕ+ suc y ≡ suc x ℕ+ y
  flip-suc zero y = refl
  flip-suc (suc x) y = cong suc (flip-suc x y)

  telescope+ : (x y z : ℤ) → (x - y) + (y - z) ≡ x - z
  telescope+ x y z =
    begin
      (x - y) + (y - z)
    ≡⟨ ℤ-CR.+-assoc x (- y) (y - z) ⟩
      x + ((- y) + (y - z))
    ≡⟨ cong (_+_ x) (sym (ℤ-CR.+-assoc (- y) y (- z))) ⟩
      x + ((- y + y) - z)
    ≡⟨ sym (ℤ-CR.+-assoc x (- y + y) (- z)) ⟩
      x + (- y + y) - z
    ≡⟨ cong (λ a → x + a - z) (proj₁ ℤ-CR.-‿inverse y) ⟩
      x + (+ 0) - z
    ≡⟨ cong (λ a → a - z) (proj₂ ℤ-CR.+-identity x) ⟩
      x - z
    ∎

  telescope- : (x y z : ℤ) → (x + y) - (x + z) ≡ y - z
  telescope- x y z =
    begin
      (x + y) - (x + z)
    ≡⟨ cong (λ a → a - (x + z)) (ℤ-CR.+-comm x y) ⟩
      (y + x) - (x + z)
    ≡⟨ ℤ-CR.+-assoc y x (- (x + z)) ⟩
      y + (x - (x + z))
    ≡⟨ cong (λ a → y + (x + a)) (lem x z) ⟩
      y + (x + (- x - z))
    ≡⟨ cong (λ a → y + a) (sym (ℤ-CR.+-assoc x (- x) (- z))) ⟩
      y + (x - x - z)
    ≡⟨ cong (λ a → y + (a - z)) (proj₂ ℤ-CR.-‿inverse x) ⟩
      y + (+ 0 - z)
    ≡⟨ cong (λ a → y + a) (proj₁ ℤ-CR.+-identity (- z)) ⟩
      y - z
    ∎
    where
    flip-⊖ : (x y : ℕ) → x ⊖ y ≡ - (y ⊖ x)
    flip-⊖ zero     zero    = refl
    flip-⊖ zero     (suc y) = refl
    flip-⊖ (suc x)  zero    = refl
    flip-⊖ (suc x)  (suc y) = flip-⊖ x y

    lem : (x y : ℤ) → - (x + y) ≡ - x - y
    lem -[1+ x ] -[1+ y ] = cong (+_ ∘ suc) (sym (flip-suc x y))
    lem -[1+ x ] (+ zero) = cong (+_ ∘ suc) (sym (proj₂ ℕ-CS.+-identity x))
    lem -[1+ x ] (+ suc y) = sym (flip-⊖ x y)
    lem (+ zero) -[1+ y ] = refl
    lem (+ suc x) -[1+ y ] = sym (flip-⊖ y x)
    lem (+ zero) (+ y) = sym (proj₁ ℤ-CR.+-identity (- (+ y)))
    lem (+ suc x) (+ zero) = cong -[1+_] (proj₂ ℕ-CS.+-identity x)
    lem (+ suc x) (+ suc y) = cong -[1+_] (flip-suc x y)

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

    private
      abs-⊖-comm : (x y : ℕ) → ∣ x ⊖ y ∣ ≡ ∣ y ⊖ x ∣
      abs-⊖-comm zero zero = refl
      abs-⊖-comm zero (suc _) = refl
      abs-⊖-comm (suc _) zero = refl
      abs-⊖-comm (suc x) (suc y) = abs-⊖-comm x y

      ∸-*-distrib : {n : ℕ} → (p q : ℕ) → p * n ∸ q * n ≡ (p ∸ q) * n
      ∸-*-distrib zero zero = refl
      ∸-*-distrib {n} zero (suc q) = 0∸n≡0 (n ℕ+ q * n)
      ∸-*-distrib (suc p) zero = refl
      ∸-*-distrib {n} (suc p) (suc q) =
        begin
          (n ℕ+ p * n) ∸ (n ℕ+ q * n)
        ≡⟨ [i+j]∸[i+k]≡j∸k n (p * n) (q * n) ⟩
          p * n ∸ q * n
        ≡⟨ ∸-*-distrib p q ⟩
          (p ∸ q) * n
        ∎

      abs-flip : (x y : ℤ) → ∣ x - y ∣ ≡ ∣ y - x ∣
      abs-flip -[1+ x ] -[1+ y ] = abs-⊖-comm y x
      abs-flip -[1+ x ] (+ y) =
        begin
          ∣ -[1+ x ] - (+ y) ∣
        ≡⟨ cong ∣_∣ (neg-minus-pos x y) ⟩
          suc (y ℕ+ x)
        ≡⟨ cong suc (ℕ-CS.+-comm y x)⟩
          suc (x ℕ+ y)
        ≡⟨ ℕ-CS.+-comm (suc x) y ⟩
          y ℕ+ suc x
        ∎
      abs-flip (+ x) -[1+ y ] =
        begin
          x ℕ+ suc y
        ≡⟨ ℕ-CS.+-comm x (suc y) ⟩
          suc (y ℕ+ x)
        ≡⟨ cong suc (ℕ-CS.+-comm y x) ⟩
          suc (x ℕ+ y)
        ≡⟨ cong ∣_∣ (sym (neg-minus-pos y x)) ⟩
          ∣ -[1+ y ] + - (+ x) ∣
        ∎
      abs-flip (+ x) (+ y) =
        begin
          ∣ (+ x) - (+ y) ∣
        ≡⟨ cong ∣_∣ (lem x y) ⟩
          ∣ x ⊖ y ∣
        ≡⟨ abs-⊖-comm x y ⟩
          ∣ y ⊖ x ∣
        ≡⟨ cong ∣_∣ (sym (lem y x)) ⟩
          ∣ (+ y) - (+ x) ∣
        ∎
        where
        lem : (x y : ℕ) → (+ x) - (+ y) ≡ x ⊖ y
        lem zero zero = refl
        lem zero (suc y) = refl
        lem (suc x) zero = cong (+_ ∘ suc) (proj₂ ℕ-CS.+-identity x)
        lem (suc x) (suc y) = refl

      diff-x<y : ∀ {x y} (x<y : x < y) → y ⊖ suc x ≡ + (y ∸ suc x)
      diff-x<y (s≤s z≤n) = refl
      diff-x<y (s≤s (s≤s y≤n)) = diff-x<y (s≤s y≤n)

      diff-x≥y : ∀ {x y} (x≥y : x ≥ y) → y ⊖ suc x ≡ -[1+ (x ∸ y) ]
      diff-x≥y z≤n = refl
      diff-x≥y (s≤s m≤n) = diff-x≥y m≤n

      >-weaken : ∀ {n m} → n > m → n ≥ m
      >-weaken (s≤s z≤n) = z≤n
      >-weaken (s≤s (s≤s m≤n)) = s≤s (>-weaken (s≤s m≤n))

      ≡-weaken : ∀ {n m} → n ≡ m → n ≥ m
      ≡-weaken {zero} refl = z≤n
      ≡-weaken {suc n} refl = s≤s (≡-weaken refl)

      suc-∸ : ∀ {x y} (y≤x : y ≤ x) → suc (x ∸ y) ≡ suc x ∸ y
      suc-∸ {x} {zero} z≤n = refl
      suc-∸ {suc x} {suc y} (s≤s y≤x) = suc-∸ y≤x
      suc-∸ {zero} {suc y} ()

      div-diff : ∀ {n : ℕ} → {x y : ℕ} → n ∣ suc x → n ∣ y → n ∣ ∣ y ⊖ suc x ∣
      div-diff {n} {x} {y} (divides q eq) (divides r eq′) = dispatch
        where
        lem-x<y : (x<y : x < y) → n ∣ ∣ y ⊖ suc x ∣
        lem-x<y x<y = divides (r ∸ q) eq″
          where
          eq″ : ∣ y ⊖ suc x ∣ ≡ (r ∸ q) * n
          eq″ =
            begin
              ∣ y ⊖ suc x ∣
            ≡⟨ cong ∣_∣ (diff-x<y x<y) ⟩
              y ∸ suc x
            ≡⟨ cong₂ _∸_ eq′ eq ⟩
              r * n ∸ q * n
            ≡⟨ ∸-*-distrib r q ⟩
              (r ∸ q) * n
            ∎

        lem-x≥y : (x≥y : x ≥ y) → n ∣ ∣ y ⊖ suc x ∣
        lem-x≥y x≥y = divides (q ∸ r) eq″
          where
          eq″ : ∣ y ⊖ suc x ∣ ≡ (q ∸ r) * n
          eq″ =
            begin
              ∣ y ⊖ suc x ∣
            ≡⟨ cong ∣_∣ (diff-x≥y x≥y) ⟩
              suc (x ∸ y)
            ≡⟨ suc-∸ x≥y ⟩
              suc x ∸ y
            ≡⟨ cong₂ _∸_ eq eq′ ⟩
              q * n ∸ r * n
            ≡⟨ ∸-*-distrib q r ⟩
              (q ∸ r) * n
            ∎

        dispatch : n ∣ ∣ y ⊖ suc x ∣
        dispatch with ℕ-Ord.compare x y
        dispatch | tri< x<y  _    _    = lem-x<y x<y
        dispatch | tri≈ _    x≡y  _    = lem-x≥y (≡-weaken x≡y)
        dispatch | tri> _    _    x>y  = lem-x≥y (>-weaken x>y)


      ∣-abs-+ : ∀ {n : ℕ} → (x y : ℤ) → n ∣ ∣ x ∣ → n ∣ ∣ y ∣ → n ∣ ∣ x + y ∣
      ∣-abs-+ {n} (+ x) (+ y) (divides q eq) (divides r eq′) = divides (q ℕ+ r) lem
        where
        lem : x ℕ+ y ≡ (q ℕ+ r) * n
        lem =
          begin
            x ℕ+ y
          ≡⟨ cong₂ _ℕ+_ eq eq′ ⟩
            q * n ℕ+ r * n
          ≡⟨ sym (proj₂ ℕ-CS.distrib n q r) ⟩
            (q ℕ+ r) * n
          ∎
      ∣-abs-+ {n} -[1+ x ] -[1+ y ] (divides q eq) (divides r eq′) = divides (q ℕ+ r) lem
        where
        lem : suc (suc (x ℕ+ y)) ≡ (q ℕ+ r) * n
        lem =
          begin
            suc ((suc x) ℕ+ y)
          ≡⟨ cong suc (ℕ-CS.+-comm (suc x) y) ⟩
            suc y ℕ+ suc x
          ≡⟨ ℕ-CS.+-comm (suc y) (suc x) ⟩
            suc x ℕ+ suc y
          ≡⟨ cong₂ _ℕ+_ eq eq′ ⟩
            q * n ℕ+ r * n
          ≡⟨ sym (proj₂ ℕ-CS.distrib n q r) ⟩
            (q ℕ+ r) * n
          ∎
      ∣-abs-+ {n} -[1+ x ] (+ y) d d′ = div-diff d d′
      ∣-abs-+ {n} (+ x) -[1+ y ] d d′ = div-diff d′ d

    reflexive : Reflexive _∼_
    reflexive {x} = divides zero (lem x)
      where
      lem : (x : ℤ) → ∣ x - x ∣ ≡ 0
      lem -[1+ x ] = cong ∣_∣ (n⊖n≡0 x)
      lem (+ zero) = refl
      lem (+ suc x) = cong ∣_∣ (n⊖n≡0 x)

    symmetric : Symmetric _∼_
    symmetric {x} {y} (divides q eq) = divides q (trans (abs-flip y x) eq)

    transitive : Transitive _∼_
    transitive {x} {y} {z} d d′ = subst (_∣_ n) (cong ∣_∣ (telescope+ x y z)) (∣-abs-+ (x - y) (y - z) d d′)



Mod : ℕ → Set
Mod n = Quotient (Mod₀ n)

plus₁ : ∀ {n} → ℤ → Mod n → Mod n
plus₁ {n} x = rec (Mod n) (λ y → [ x + y ])
                  (λ {y} {y′} y∼y′ → [ subst (_∣_ n) (cong ∣_∣ (sym (telescope- x y y′))) y∼y′ ]-cong)

plus : ∀ {n} → Mod n → Mod n → Mod n
plus {n} = rec (Mod n → Mod n) plus₁ (λ {x} {x′} x∼x′ → extensionality (plus₁ x) (plus₁ x′) (lem x x′ x∼x′))
  where
  extensionality : {A B : Set} → (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g
  extensionality = {!!}

  lem : (x x′ : ℤ) → (x∼x′ : n ∣ ∣ x - x′ ∣) → (y : Mod n) → plus₁ x y ≡ plus₁ x′ y
  lem x x′ x∼x′ = elim _ (λ y → [ proof y ]-cong) (λ x∼x′ → proof-irrelevance _ _)
    where
    eq : (y : ℤ) → (x + y) - (x′ + y) ≡ x - x′
    eq y =
      begin
        (x + y) - (x′ + y)
      ≡⟨ cong₂ _-_ (ℤ-CR.+-comm x y) (ℤ-CR.+-comm x′ y) ⟩
        (y + x) - (y + x′)
      ≡⟨ telescope- y x x′ ⟩
        x - x′
      ∎

    proof : (y : ℤ) → n ∣ ∣ (x + y) - (x′ + y) ∣
    proof y = subst (_∣_ n) (cong ∣_∣ (sym (eq y))) x∼x′

_+1 : ∀ {n} → Mod n → Mod n
_+1 = plus [ + 1 ]

_-1 : ∀ {n} → Mod n → Mod n
_-1 = plus [ - (+ 1) ]

+1-1 : ∀ {n} → (x : Mod n) → x +1 -1 ≡ x
+1-1 {n} = elim _ (λ x → [ proof x ]-cong) (λ x∼y → proof-irrelevance _ _)
  where
  proof : ∀ x → n ∣ ∣ ℤpred (ℤsuc x) - x ∣
  proof x = divides 0 (cong ∣_∣ (lem x))
    where
    lem : ∀ {k} → ∀ x → -[1+ k ] + (+ (suc k) + x) - x ≡ + 0
    lem {k} x =
      begin
        -[1+ k ] + (+ suc k + x) - x
      ≡⟨ cong (λ a → a - x) (sym (ℤ-CR.+-assoc -[1+ k ] (+ suc k) x)) ⟩
        (-[1+ k ] + (+ suc k)) + x - x
      ≡⟨ cong (λ a → a + x - x) {k ⊖ k} refl ⟩
        ((- (+ suc k)) + (+ suc k)) + x - x
      ≡⟨ cong (λ a → a + x - x) (proj₁ ℤ-CR.-‿inverse -[1+ k ]) ⟩
        + 0 + x - x
      ≡⟨ cong (λ z → z - x) (proj₁ ℤ-CR.+-identity x) ⟩
        x - x
      ≡⟨ proj₂ ℤ-CR.-‿inverse x ⟩
        + 0
      ∎


