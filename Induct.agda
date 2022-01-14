module Induct where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
    begin
        (zero + n) + p
    ≡⟨⟩
        n + p
    ≡⟨⟩
        zero + (n + p)
    ∎
+-assoc (suc m) n p =
    begin
        (suc m + n) + p
    ≡⟨⟩
        suc (m + n) + p
    ≡⟨⟩
        suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
        suc (m + (n + p))
    ≡⟨⟩
        suc m + (n + p)
    ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
    begin
        (2 + n) + p
    ≡⟨⟩
        suc (1 + n) + p
    ≡⟨⟩
        suc ((1 + n) + p)
    ≡⟨ cong suc (+-assoc-1 n p) ⟩
        suc (1 + (n + p))
    ≡⟨⟩
        2 + (n + p)
    ∎
    where
    +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
    +-assoc-1 n p =
        begin
            (1 + n) + p
        ≡⟨⟩
            suc (0 + n) + p
        ≡⟨⟩
            suc ((0 + n) + p)
        ≡⟨ cong suc (+-assoc-0 n p) ⟩
            suc (0 + (n + p))
        ≡⟨⟩
            1 + (n + p)
        ∎
        where
        +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
        +-assoc-0 n p =
            begin
                (0 + n) + p
            ≡⟨⟩
                n + p
            ≡⟨⟩
                0 + (n + p)
            ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
    begin
        zero + zero
    ≡⟨⟩
        zero
    ∎
+-identityʳ (suc m) =
    begin
        (suc m) + zero
    ≡⟨⟩
        suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩
        suc m
    ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
    begin
        zero + suc n
    ≡⟨⟩
        suc n
    ≡⟨⟩
        suc (zero + n)
    ∎
+-suc (suc m) n =
    begin
        suc m + suc n
    ≡⟨⟩
        suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
        suc (suc (m + n))
    ≡⟨⟩
        suc (suc m + n)
    ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
    begin
        m + zero
    ≡⟨ +-identityʳ m ⟩
        m
    ≡⟨⟩
        zero + m
    ∎
+-comm m (suc n) =
    begin
        m + suc n
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨⟩
        suc n + m
    ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
    begin
        (m + n) + (p + q)
    ≡⟨ +-assoc m n (p + q) ⟩
        m + (n + (p + q))
    ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
        m + ((n + p) + q)
    ≡⟨ sym (+-assoc m (n + p) q) ⟩
        (m + (n + p)) + q
    ∎

-- finite-+-assoc
-- (0 + n) + p ≡ 0 + (n + p)
-- (1 + n) + p ≡ 1 + (n + p)
-- (2 + n) + p ≡ 2 + (n + p)
-- (3 + n) + p ≡ 3 + (n + p)
-- ...
-- (m + n) + p ≡ m + (n + p)

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl  
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl  

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl  
+-swap (suc m) n p rewrite sym (+-assoc m n p) | cong (_+ p) (+-comm m n) | +-assoc n m p | sym (+-suc n (m + p)) = refl  


lemma₁ : ∀ (m : ℕ) → m * zero ≡ zero
lemma₁ zero = refl  
lemma₁ (suc m) rewrite lemma₁ m = refl

lemma₂ : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
lemma₂ zero n = refl  
lemma₂ (suc m) n rewrite lemma₂ m n =
    begin
        suc (n + (m + m * n))
    ≡⟨ cong suc (cong (n +_) (+-comm m (m * n))) ⟩
        suc (n + (m * n + m))
    ≡⟨ cong suc (sym (+-assoc n (m * n) m)) ⟩
        suc ((n + m * n) + m)
    ≡⟨ cong suc (+-comm (n + m * n) m) ⟩
        suc (m + (n + m * n))
    ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n zero rewrite lemma₁ (m + n) | lemma₁ m | lemma₁ n = refl  
*-distrib-+ m n (suc p) =
    begin
        (m + n) * suc p
    ≡⟨ lemma₂ (m + n) p ⟩
        m + n + (m + n) * p
    ≡⟨ cong ((m + n) +_) (*-distrib-+ m n p) ⟩
        m + n + (m * p + n * p)
    ≡⟨ +-rearrange m n (m * p) (n * p) ⟩
        m + (n + m * p) + n * p
    ≡⟨ cong (_+ (n * p)) (cong (m +_) (+-comm n (m * p))) ⟩
        m + (m * p + n) + n * p
    ≡⟨ sym (+-rearrange m (m * p) n (n * p)) ⟩
        (m + m * p) + (n + n * p)
    ≡⟨ cong (_+ (n + n * p)) (sym (lemma₂ m p)) ⟩
        m * suc p + (n + n * p)
    ≡⟨ cong ((m * suc p) +_) (sym (lemma₂ n p)) ⟩
        m * suc p + n * suc p
    ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | cong (n * p +_) (*-assoc m n p) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite lemma₁ m = refl
*-comm m (suc n) rewrite lemma₂ m n | cong (m +_) (*-comm m n) = refl

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

lemma₃ : ∀ (m n : ℕ) → suc m ∸ n ≡ suc (m ∸ n)
lemma₃ m zero = refl
lemma₃ m (suc n) =
  begin
    suc m ∸ suc n
  ≡⟨⟩
    {!   !}

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m n zero rewrite +-identityʳ n = refl
∸-+-assoc m n (suc p) = {!   !}
