module Data.Mod.Lemmas where

open import Data.Nat renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Nat.Properties
open import Data.Integer hiding (_≤_) renaming (suc to ℤsuc; pred to ℤpred)
open import Data.Nat.Divisibility
open import Function using (_∘_; _⟨_⟩_)

open import Relation.Binary

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

  open import Data.Nat.Coprimality hiding (sym)
  open import Data.Nat.Primality
  open import Data.Empty
  open import Data.Fin using (Fin; toℕ; fromℕ≤; #_)
  open import Data.Fin.Props

  prime⇒coprime : ∀ n → Prime n → ∀ x → (suc x) < n → Coprime n (suc x)
  prime⇒coprime zero () x x<n {i} (i∣n , i∣x)
  prime⇒coprime (suc zero) () x x<n {i} (i∣n , i∣x)
  prime⇒coprime (suc (suc n)) p x x<n {zero} (divides q eq , i∣x) = ⊥-elim bot
    where
    contradiction : suc (suc n) ≡ 0
    contradiction =
      begin
        suc (suc n)
      ≡⟨ eq ⟩
        q ℕ* 0
      ≡⟨ proj₂ ℕ-CS.zero q ⟩
        0
      ∎

    bot : ⊥
    bot with contradiction
    bot | ()
  prime⇒coprime (suc (suc n)) p x x<n {suc zero} (i∣n , i∣x) = refl
  prime⇒coprime (suc (suc n)) p x x<n {suc (suc i)} (i∣n , i∣x) = ⊥-elim (p (proj₁ fin) (proj₂ fin))
    where
    i≤x : suc (suc i) ≤ suc x
    i≤x = ∣⇒≤ i∣x

    ssi<ssn : suc (suc i) < suc (suc n)
    ssi<ssn = s≤s i≤x ⟨ trans ⟩ x<n
      where
      open DecTotalOrder Data.Nat.decTotalOrder

    i<n : i < n
    i<n = ≤-pred (≤-pred ssi<ssn)

    fin : ∃ λ (k : Fin n) → suc (suc (toℕ k)) ∣ suc (suc n)
    fin = fromℕ≤ i<n , subst (λ ξ → ξ ∣ suc (suc n)) (sym (cong (suc ∘ suc) (toℕ-fromℕ≤ i<n))) i∣n


  open import Data.Nat.GCD
  open import Data.Nat.DivMod

  mod-suc : ∀ n x → suc (suc n) ∣ suc (x ℕ* (suc (suc n))) ℕ+ suc n
  mod-suc n x = divides (suc x) eq
    where
    open Nat.SemiringSolver
    eq : suc (x ℕ* suc (suc n)) ℕ+ suc n ≡ suc x ℕ* suc (suc n)
    eq = solve 2 (λ a b → con 1 :+ a :* (con 1 :+ b) :+ b := (con 1 :+ a) :* (con 1 :+ b)) refl x (suc n)

  ∣-inv : ∀ n x → Coprime (suc (suc n)) x → ∃ λ y → suc (suc n) ∣ (y ℕ* x) ℕ+ (suc n)
  ∣-inv n x coprime with Bézout.identity (coprime-gcd coprime)
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
