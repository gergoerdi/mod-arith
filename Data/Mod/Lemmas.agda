module Data.Mod.Lemmas where

open import Data.Nat renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Nat.Properties
open import Data.Integer hiding (_≤_) renaming (suc to ℤsuc; pred to ℤpred)
open import Data.Integer.Properties
open import Data.Nat.Divisibility
open import Function using (_∘_; _⟨_⟩_)

open import Relation.Binary

open import Algebra
import Data.Nat.Properties as Nat
private
  module ℕ-CS = CommutativeSemiring Nat.commutativeSemiring
private
  module ℕ-Ord = StrictTotalOrder Nat.strictTotalOrder
import Data.Integer.Properties as Integer
private
  module ℤ-CR = CommutativeRing Integer.commutativeRing

open import Data.Product

open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong; cong₂; subst)
open PropEq.≡-Reasoning

abstract
  neg-minus-pos : (x y : ℕ) → -[1+ x ] - (+ y) ≡ -[1+ (y ℕ+ x) ]
  neg-minus-pos x zero = refl
  neg-minus-pos zero (suc y) = cong (-[1+_] ∘ suc) (sym (proj₂ ℕ-CS.+-identity y))
  neg-minus-pos (suc x) (suc y) = cong (-[1+_] ∘ suc) (ℕ-CS.+-comm (suc x) y)

  flip-suc : ∀ x y → x ℕ+ suc y ≡ suc x ℕ+ y
  flip-suc zero y = refl
  flip-suc (suc x) y = cong suc (flip-suc x y)

  flip-⊖ : (x y : ℕ) → x ⊖ y ≡ - (y ⊖ x)
  flip-⊖ zero     zero    = refl
  flip-⊖ zero     (suc y) = refl
  flip-⊖ (suc x)  zero    = refl
  flip-⊖ (suc x)  (suc y) = flip-⊖ x y

  telescope : (x y z : ℤ) → (x - y) + (y - z) ≡ x - z
  telescope x y z =
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

  abs-⊖-comm : (x y : ℕ) → ∣ x ⊖ y ∣ ≡ ∣ y ⊖ x ∣
  abs-⊖-comm zero zero = refl
  abs-⊖-comm zero (suc _) = refl
  abs-⊖-comm (suc _) zero = refl
  abs-⊖-comm (suc x) (suc y) = abs-⊖-comm x y

  ∸-*-distrib : {n : ℕ} → (p q : ℕ) → p ℕ* n ∸ q ℕ* n ≡ (p ∸ q) ℕ* n
  ∸-*-distrib zero zero = refl
  ∸-*-distrib {n} zero (suc q) = 0∸n≡0 (n ℕ+ q ℕ* n)
  ∸-*-distrib (suc p) zero = refl
  ∸-*-distrib {n} (suc p) (suc q) =
    begin
      (n ℕ+ p ℕ* n) ∸ (n ℕ+ q ℕ* n)
    ≡⟨ [i+j]∸[i+k]≡j∸k n (p ℕ* n) (q ℕ* n) ⟩
      p ℕ* n ∸ q ℕ* n
    ≡⟨ ∸-*-distrib p q ⟩
      (p ∸ q) ℕ* n
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
      eq″ : ∣ y ⊖ suc x ∣ ≡ (r ∸ q) ℕ* n
      eq″ =
        begin
          ∣ y ⊖ suc x ∣
        ≡⟨ cong ∣_∣ (diff-x<y x<y) ⟩
          y ∸ suc x
        ≡⟨ cong₂ _∸_ eq′ eq ⟩
          r ℕ* n ∸ q ℕ* n
        ≡⟨ ∸-*-distrib r q ⟩
          (r ∸ q) ℕ* n
        ∎

    lem-x≥y : (x≥y : x ≥ y) → n ∣ ∣ y ⊖ suc x ∣
    lem-x≥y x≥y = divides (q ∸ r) eq″
      where
      eq″ : ∣ y ⊖ suc x ∣ ≡ (q ∸ r) ℕ* n
      eq″ =
        begin
          ∣ y ⊖ suc x ∣
        ≡⟨ cong ∣_∣ (diff-x≥y x≥y) ⟩
          suc (x ∸ y)
        ≡⟨ suc-∸ x≥y ⟩
          suc x ∸ y
        ≡⟨ cong₂ _∸_ eq eq′ ⟩
          q ℕ* n ∸ r ℕ* n
        ≡⟨ ∸-*-distrib q r ⟩
          (q ∸ r) ℕ* n
        ∎

    dispatch : n ∣ ∣ y ⊖ suc x ∣
    dispatch with ℕ-Ord.compare x y
    dispatch | tri< x<y  _    _    = lem-x<y x<y
    dispatch | tri≈ _    x≡y  _    = lem-x≥y (≡-weaken x≡y)
    dispatch | tri> _    _    x>y  = lem-x≥y (>-weaken x>y)


  ∣-abs-+ : ∀ {n : ℕ} → (x y : ℤ) → n ∣ ∣ x ∣ → n ∣ ∣ y ∣ → n ∣ ∣ x + y ∣
  ∣-abs-+ {n} (+ x) (+ y) (divides q eq) (divides r eq′) = divides (q ℕ+ r) lem
    where
    lem : x ℕ+ y ≡ (q ℕ+ r) ℕ* n
    lem =
      begin
        x ℕ+ y
      ≡⟨ cong₂ _ℕ+_ eq eq′ ⟩
        q ℕ* n ℕ+ r ℕ* n
      ≡⟨ sym (proj₂ ℕ-CS.distrib n q r) ⟩
        (q ℕ+ r) ℕ* n
      ∎
  ∣-abs-+ {n} -[1+ x ] -[1+ y ] (divides q eq) (divides r eq′) = divides (q ℕ+ r) lem
    where
    lem : suc (suc (x ℕ+ y)) ≡ (q ℕ+ r) ℕ* n
    lem =
      begin
        suc ((suc x) ℕ+ y)
      ≡⟨ cong suc (ℕ-CS.+-comm (suc x) y) ⟩
        suc y ℕ+ suc x
      ≡⟨ ℕ-CS.+-comm (suc y) (suc x) ⟩
        suc x ℕ+ suc y
      ≡⟨ cong₂ _ℕ+_ eq eq′ ⟩
        q ℕ* n ℕ+ r ℕ* n
      ≡⟨ sym (proj₂ ℕ-CS.distrib n q r) ⟩
        (q ℕ+ r) ℕ* n
      ∎
  ∣-abs-+ {n} -[1+ x ] (+ y) d d′ = div-diff d d′
  ∣-abs-+ {n} (+ x) -[1+ y ] d d′ = div-diff d′ d

  abs-neg : ∀ x → ∣ - x ∣ ≡ ∣ x ∣
  abs-neg -[1+ x ] = refl
  abs-neg (+ zero) = refl
  abs-neg (+ suc x) = refl

  ∣-abs‿- : ∀ {n : ℕ} → (x y : ℤ) → n ∣ ∣ x ∣ → n ∣ ∣ y ∣ → n ∣ ∣ x - y ∣
  ∣-abs‿- {n} x y d d′  = ∣-abs-+ x (- y) d (subst (_∣_ n) (sym (abs-neg y)) d′)

  ∣-abs-*ˡ : ∀ {n} x y → n ∣ ∣ y ∣ → n ∣ ∣ x * y ∣
  ∣-abs-*ˡ {n} x y (divides q eq) = divides (∣ x ∣ ℕ* q) lem
    where
    lem : ∣ x * y ∣ ≡ ∣ x ∣ ℕ* q ℕ* n
    lem =
      begin
        ∣ x * y ∣
      ≡⟨ Integer.abs-*-commute x y ⟩
        ∣ x ∣ ℕ* ∣ y ∣
      ≡⟨ cong (λ ξ → ∣ x ∣ ℕ* ξ) eq ⟩
        ∣ x ∣ ℕ* (q ℕ* n)
      ≡⟨ sym (ℕ-CS.*-assoc ∣ x ∣ q n) ⟩
        ∣ x ∣ ℕ* q ℕ* n
      ∎

  ∣-abs-*ʳ : ∀ {n} x y → n ∣ ∣ x ∣ → n ∣ ∣ x * y ∣
  ∣-abs-*ʳ {n} x y (divides q eq) = divides (q ℕ* ∣ y ∣) lem
    where
    lem : ∣ x * y ∣ ≡ q ℕ* ∣ y ∣ ℕ* n
    lem =
      begin
        ∣ x * y ∣
      ≡⟨ Integer.abs-*-commute x y ⟩
        ∣ x ∣ ℕ* ∣ y ∣
      ≡⟨ cong (λ ξ → ξ ℕ* ∣ y ∣) eq ⟩
        q ℕ* n ℕ* ∣ y ∣
      ≡⟨ ℕ-CS.*-assoc q n ∣ y ∣ ⟩
        q ℕ* (n ℕ* ∣ y ∣)
      ≡⟨ cong (λ ξ → q ℕ* ξ) (ℕ-CS.*-comm n ∣ y ∣) ⟩
        q ℕ* (∣ y ∣ ℕ* n)
      ≡⟨ sym (ℕ-CS.*-assoc q ∣ y ∣ n) ⟩
        q ℕ* ∣ y ∣ ℕ* n
      ∎

  ∣-abs-neg : ∀ {n} x y → n ∣ ∣ x - y ∣ → n ∣ ∣ (- x) - (- y) ∣
  ∣-abs-neg {n} x y = subst (_∣_ n) lem
    where
    open Integer.RingSolver

    lem : ∣ x - y ∣ ≡ ∣ (- x) - (- y) ∣
    lem =
      begin
        ∣ x - y ∣
      ≡⟨ cong ∣_∣ (solve 2 (λ x y → x :- y := :- (:- x :- :- y)) refl x y) ⟩
        ∣ - ((- x) - (- y)) ∣
      ≡⟨ abs-neg ((- x) - (- y)) ⟩
        ∣ (- x) - (- y) ∣
      ∎

  _+-*-+_ : ∀ x y → (+ x) * (+ y) ≡ + (x ℕ* y)
  zero +-*-+ y = refl
  suc x +-*-+ zero = x +-*-+ zero
  suc x +-*-+ suc y = refl

  mod-suc : ∀ n x → suc (suc n) ∣ suc (x ℕ* (suc (suc n))) ℕ+ suc n
  mod-suc n x = divides (suc x) eq
    where
    open Nat.SemiringSolver
    eq : suc (x ℕ* suc (suc n)) ℕ+ suc n ≡ suc x ℕ* suc (suc n)
    eq = solve 2 (λ a b → con 1 :+ a :* (con 1 :+ b) :+ b := (con 1 :+ a) :* (con 1 :+ b)) refl x (suc n)

  open import Data.Nat.GCD
  open import Data.Nat.DivMod
  open import Data.Nat.Coprimality hiding (sym)

  ∣-inv : ∀ n x → Coprime (suc (suc n)) x → ∃ λ y → suc (suc n) ∣ (y ℕ* x) ℕ+ (suc n)
  ∣-inv n x coprime with coprime-Bézout coprime
  ∣-inv n x coprime | Bézout.-+ α β eq = β , lem
    where
    lem : suc (suc n) ∣ β ℕ* x ℕ+ suc n
    lem = subst (λ ξ → suc (suc n) ∣ ξ ℕ+ suc n) eq (mod-suc n α)
  ∣-inv n x coprime | Bézout.+- α β eq = β ℕ* suc n , lem
    where
    lem : suc (suc n) ∣ β ℕ* suc n ℕ* x ℕ+ suc n
    lem = divides (α ℕ* suc n) eq′
      where
      eq′ : β ℕ* suc n ℕ* x ℕ+ suc n ≡ α ℕ* suc n ℕ* suc (suc n)
      eq′ =
        begin
          β ℕ* suc n ℕ* x ℕ+ suc n
        ≡⟨ cong (λ ξ → ξ ℕ+ suc n) (ℕ-CS.*-assoc β (suc n) x) ⟩
          β ℕ* (suc n ℕ* x) ℕ+ suc n
        ≡⟨ cong (λ ξ → ξ ℕ+ suc n) (sym (cong (_ℕ*_ β) (ℕ-CS.*-comm x (suc n)))) ⟩
          β ℕ* (x ℕ* suc n) ℕ+ suc n
        ≡⟨ cong (λ ξ → ξ ℕ+ suc n) (sym (ℕ-CS.*-assoc β x (suc n))) ⟩
          β ℕ* x ℕ* suc n ℕ+ suc n
        ≡⟨ ℕ-CS.+-comm (β ℕ* x ℕ* suc n) (suc n) ⟩
          suc n ℕ+ β ℕ* x ℕ* suc n
        ≡⟨ refl ⟩
          suc (β ℕ* x) ℕ* suc n
        ≡⟨ cong (λ ξ → ξ ℕ* suc n) eq ⟩
          α ℕ* suc (suc n) ℕ* suc n
        ≡⟨ ℕ-CS.*-assoc α (suc (suc n)) (suc n) ⟩
          α ℕ* (suc (suc n) ℕ* suc n)
        ≡⟨ sym (cong (λ ξ → α ℕ* ξ) (ℕ-CS.*-comm (suc n) (suc (suc n)))) ⟩
          α ℕ* (suc n ℕ* suc (suc n))
        ≡⟨ sym (ℕ-CS.*-assoc α (suc n) (suc (suc n))) ⟩
          α ℕ* suc n ℕ* suc (suc n)
        ∎

  *-shift : ∀ n x y → (+ y) * (+ x) - (+ 1) ≡ + (y ℕ* x ℕ+ n) - (+ suc n)
  *-shift n x y =
    begin
      (+ y) * (+ x) - (+ 1)
    ≡⟨ cong (λ ξ → ξ - (+ 1)) (y +-*-+ x) ⟩
      + (y ℕ* x) - (+ 1)
    ≡⟨ cong (λ ξ → + (y ℕ* x) + ξ) (lem n) ⟩
      + (y ℕ* x) + ((+ n) - (+ suc n))
    ≡⟨ sym (ℤ-CR.+-assoc (+ (y ℕ* x)) (+ n) -[1+ n ]) ⟩
      + (y ℕ* x) + (+ n) - (+ suc n)
    ≡⟨ refl ⟩
      + (y ℕ* x ℕ+ n) - (+ suc n)
    ∎
    where
    lem : ∀ a → - (+ 1) ≡ (+ a) - (+ suc a)
    lem zero = refl
    lem (suc a) = lem a

  ⊖-cancel : ∀ x y → x ℕ+ y ⊖ x ≡ + y
  ⊖-cancel zero y = refl
  ⊖-cancel (suc x) y = ⊖-cancel x y

  open import Data.Empty

  ∣-abs-inv : ∀ n x → Coprime (suc (suc n)) ∣ x ∣ → ∃ λ y → suc (suc n) ∣ ∣ y * x - (+ 1) ∣
  ∣-abs-inv n (+ x) coprime with ∣-inv n x coprime
  ∣-abs-inv n (+ x) coprime | y , divides zero eq = ⊥-elim (i+1+j≢i 0 contradiction)
    where
    contradiction : suc (y ℕ* x ℕ+ n) ≡ zero
    contradiction =
      begin
        suc (y ℕ* x ℕ+ n)
      ≡⟨ cong suc (sym (ℕ-CS.+-comm n (y ℕ* x))) ⟩
        suc (n ℕ+ y ℕ* x)
      ≡⟨ ℕ-CS.+-comm (suc n) (y ℕ* x) ⟩
        y ℕ* x ℕ+ suc n
      ≡⟨ eq ⟩
        0
      ∎
  ∣-abs-inv n (+ x) coprime | y , divides (suc q) eq = + y , divides q eq′
    where
    eq′ : ∣ (+ y) * (+ x) - (+ 1) ∣ ≡ q ℕ* suc (suc n)
    eq′ =
      begin
        ∣ (+ y) * (+ x) - (+ 1) ∣
      ≡⟨ cong ∣_∣ (*-shift (suc n) x y) ⟩
        ∣ (y ℕ* x ℕ+ (suc n)) ⊖ suc (suc n) ∣
      ≡⟨ cong (λ ξ → ∣ + ξ - (+ suc (suc n)) ∣) eq ⟩
        ∣ suc (suc n) ℕ+ q ℕ* suc (suc n) ⊖ suc (suc n) ∣
      ≡⟨ cong ∣_∣ (⊖-cancel n (q ℕ* suc (suc n))) ⟩
        ∣ + (q ℕ* suc (suc n)) ∣
      ≡⟨ refl ⟩
        q ℕ* suc (suc n)
      ∎

  ∣-abs-inv n -[1+ x ] coprime with ∣-inv n (suc x) coprime
  ∣-abs-inv n -[1+ x ] coprime | y , divides zero eq = ⊥-elim (i+1+j≢i 0 contradiction)
    where
    contradiction : suc n ℕ+ y ℕ* suc x ≡ 0
    contradiction =
      begin
        suc n ℕ+ y ℕ* suc x
      ≡⟨ ℕ-CS.+-comm (suc n) (y ℕ* suc x) ⟩
        y ℕ* suc x ℕ+ suc n
      ≡⟨ eq ⟩
        0
      ∎
  ∣-abs-inv n -[1+ x ] coprime | y , divides (suc q) eq = - (+ y) , divides q eq′
    where
    lem : ∀ x y → - (+ y) * -[1+ x ] ≡ (+ y) * (+ suc x)
    lem x zero = refl
    lem x (suc y) = refl

    eq′ : ∣ - (+ y) * -[1+ x ] - (+ 1) ∣ ≡ q ℕ* suc (suc n)
    eq′ =
      begin
        ∣ - (+ y) * -[1+ x ] - (+ 1) ∣
      ≡⟨ cong (λ ξ → ∣ ξ - + 1 ∣) (lem x y) ⟩
        ∣ (+ y) * (+ suc x) - (+ 1) ∣
      ≡⟨ cong ∣_∣ (*-shift (suc n) (suc x) y) ⟩
        ∣ y ℕ* suc x ℕ+ suc n ⊖ suc (suc n) ∣
      ≡⟨ cong (λ ξ → ∣ ξ ⊖ suc (suc n) ∣) eq ⟩
        ∣ n ℕ+ q ℕ* suc (suc n) ⊖ n ∣
      ≡⟨ cong ∣_∣ (⊖-cancel n (q ℕ* suc (suc n))) ⟩
        ∣ + (q ℕ* suc (suc n)) ∣
      ≡⟨ refl ⟩
        q ℕ* suc (suc n)
      ∎

