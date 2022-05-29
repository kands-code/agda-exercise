module Relations where

open import Agda.Builtin.Equality
open import Natural

data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} →
        zero ≤ n
    s≤s : ∀ {m n : ℕ} →
        m ≤ n →
        (suc m) ≤ (suc n)

infix 4 _≤_

-- example : finished by auto mode
_ : 3 ≤ 5
_ = s≤s {2} {4} (s≤s {1} {3} (s≤s {0} {2} (z≤n {2})))

inv-s≤s : ∀ {m n : ℕ}
    → suc m ≤ suc n
    → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
    → m ≤ zero
    → m ≡ zero
inv-z≤n z≤n = refl
 