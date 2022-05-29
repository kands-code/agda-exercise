module Relations where

open import Agda.Builtin.Equality
open import Natural

data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} → zero ≤ n
    s≤s : ∀ {m n : ℕ} → m ≤ n → (suc m) ≤ (suc n)

infix 4 _≤_