module Induct where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

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
*-distrib-+ m n zero
  rewrite lemma₁ (m + n) 
    | lemma₁ m 
    | lemma₁ n 
    = refl  
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
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p 
    | cong (n * p +_) (*-assoc m n p) 
    = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite lemma₁ m = refl
*-comm m (suc n)
  rewrite lemma₂ m n 
    | cong (m +_) (*-comm m n) 
    = refl

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p
  rewrite 0∸n≡0 n
    | 0∸n≡0 p
    | 0∸n≡0 (n + p)
    = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p
  rewrite ∸-+-assoc m n p
    = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) →
  m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p 
  rewrite +-comm (m ^ p) 0
    = refl
^-distribˡ-+-* m (suc n) p
  rewrite *-assoc m (m ^ n) (m ^ p)
    | cong (m *_) (^-distribˡ-+-* m n p) 
    = refl

lemma₃ : ∀ (m n : ℕ) → m ^ suc n ≡ m * (m ^ n)
lemma₃ m zero = refl
lemma₃ m (suc n) = refl

^-distribʳ-* : ∀ (m n p : ℕ) →
  (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite lemma₃ m p
    | *-assoc m n ((m * n) ^ p)
    | *-assoc m (m ^ p) (n * (n ^ p))
    | sym (*-assoc (m ^ p) n (n ^ p))
    | *-comm (m ^ p) n
    | ^-distribʳ-* m n p
    | sym (*-assoc n (m ^ p) (n ^ p))
    = refl

1^n≡1 : ∀ (n : ℕ) → 1 ^ n ≡ 1
1^n≡1 zero = refl
1^n≡1 (suc n)
  rewrite lemma₃ 1 n
    | 1^n≡1 n
    = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p
  rewrite *-comm zero p
    | 1^n≡1 p 
    = refl
^-*-assoc m (suc n) p
  rewrite ^-distribˡ-+-* m p (n * p)
    | ^-distribʳ-* m (m ^ n) p
    | ^-*-assoc m n p
    = refl

-- Bin-laws
data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I 
inc (n O) = n I  
inc (n I) = (inc n) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero  
from (n O) = 2 * from n
from (n I) = suc (2 * from n)

thm₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
thm₁ ⟨⟩ = refl
thm₁ (b O) = refl
thm₁ (b I)
  rewrite thm₁ b 
    | +-suc (from b) (suc (from b) + 0)
    | +-comm (from b) (suc (from b + 0))
    | +-comm (from b) 0 = refl

thm₃ : ∀ (n : ℕ) → from (to n) ≡ n
thm₃ zero = refl
thm₃ (suc n)
  rewrite thm₁ (to (suc n)) = {!   !}
