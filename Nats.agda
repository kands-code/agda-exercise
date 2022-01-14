module Nats where

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

seven : ℕ
seven = succ (succ (succ (succ (succ (succ (succ zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n  
(succ m) + n = succ (m + n)

_ : 2 + 3 ≡ 5
_ = refl  
-- _ =
--     begin
--         2 + 3
--     ≡⟨⟩
--         succ (succ zero) + succ (succ (succ zero))
--     ≡⟨⟩
--         succ ((succ zero) + (succ (succ (succ zero))))
--     ≡⟨⟩
--         succ (succ (zero + (succ (succ (succ zero)))))
--     ≡⟨⟩
--         succ (succ (succ (succ (succ zero))))
--     ≡⟨⟩
--         5
--     ∎

+-example =
    begin
        3 + 4
    ≡⟨⟩
        succ (succ (succ zero)) + succ (succ (succ (succ zero)))
    ≡⟨⟩
        succ ((succ (succ zero)) + (succ (succ (succ (succ zero)))))
    ≡⟨⟩
        succ (succ ((succ zero) + (succ (succ (succ (succ zero))))))
    ≡⟨⟩
        succ (succ (succ (zero + (succ (succ (succ (succ zero)))))))
    ≡⟨⟩
        succ (succ (succ (succ (succ (succ (succ zero))))))
    ≡⟨⟩
        7
    ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(succ m) * n = n + (m * n)

_ =
    begin
        2 * 3
    ≡⟨⟩
        3 + (1 * 3)
    ≡⟨⟩
        3 + (3 + (0 * 3))
    ≡⟨⟩
        3 + (3 + 0)
    ≡⟨⟩
        6
    ∎

*-example =
    begin
        3 * 4
    ≡⟨⟩
        4 + (2 * 4)
    ≡⟨⟩
        4 + (4 + (1 * 4))
    ≡⟨⟩
        4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩
        4 + (4 + (4 + 0))
    ≡⟨⟩
        12
    ∎

_^_ : ℕ → ℕ → ℕ
m ^ zero = succ zero
m ^ (succ n) = m * (m ^ n)

^-example =
    begin
        3 ^ 4
    ≡⟨⟩
        3 * (3 ^ 3)
    ≡⟨⟩
        3 * (3 * (3 ^ 2))
    ≡⟨⟩
        3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
        3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
        3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩
        81
    ∎

_#-_ : ℕ → ℕ → ℕ
m #- zero = m
zero #- succ n = zero
succ m #- succ n = m #- n

_ =
    begin
        3 #- 2
    ≡⟨⟩
        2 #- 1
    ≡⟨⟩
        1 #- 0
    ≡⟨⟩
        1
    ∎

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _#-_ #-}

data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I  
inc (n O) = n I  
inc (n I) = (inc n) O

_ =
    begin
        inc (⟨⟩ I I)
    ≡⟨⟩
        (inc (⟨⟩ I)) O
    ≡⟨⟩
        ((inc ⟨⟩) O) O
    ≡⟨⟩
        ⟨⟩ I O O
    ∎

to : ℕ → Bin
to zero = ⟨⟩ O
to (succ n) = (to n) I  

_ =
    begin
        to 3
    ≡⟨⟩
        (to 2) I
    ≡⟨⟩
        ((to 1) I) I
    ≡⟨⟩
        (((to 0) I) I) I
    ≡⟨⟩
        ⟨⟩ O I I I
    ∎

from : Bin → ℕ
from ⟨⟩ = zero  
from (n O) = 2 * (from n)
from (n I) = succ (2 * (from n))

_ =
    begin
        from (⟨⟩ I I I O)
    ≡⟨⟩
        2 * (from (⟨⟩ I I I))
    ≡⟨⟩
        2 * (succ (2 * (from (⟨⟩ I I))))
    ≡⟨⟩
        2 * (succ (2 * (succ (2 * (from (⟨⟩ I))))))
    ≡⟨⟩
        2 * (succ (2 * (succ (2 * (succ (2 * (from (⟨⟩))))))))
    ≡⟨⟩
        2 * (succ (2 * (succ (2 * (succ (2 * 0))))))
    ≡⟨⟩
        2 * (succ (2 * (succ (2 * 1))))
    ≡⟨⟩
        14
    ∎

