module Natural where

open import Agda.Builtin.Equality

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

-- seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
infixl 6 _+_
zero + b = b
(suc a) + b = suc (a + b)

{-# BUILTIN NATPLUS _+_ #-}

+-id : ∀ (a : ℕ) → a + zero ≡ zero + a
+-id zero = refl
+-id (suc a) rewrite +-id a = refl

+-comm : ∀ (a b : ℕ) → a + b ≡ b + a
+-comm zero b rewrite +-id b = refl
+-comm (suc a) zero rewrite +-id (suc a) = refl
+-comm (suc a) (suc b)
    rewrite +-comm a (suc b)
    | +-comm b (suc a)
    | +-comm a b  = refl

+-asso : ∀ (a b c : ℕ) → a + b + c ≡ a + (b + c)
+-asso zero b c = refl
+-asso (suc a) zero c
    rewrite +-id (suc a)
    | +-id a = refl
+-asso (suc a) (suc b) zero
    rewrite +-id (suc a + suc b)
    | +-id b = refl
+-asso (suc a) (suc b) (suc c)
    rewrite (+-comm a (suc b))
    | +-comm (b + a) (suc c)
    | +-comm b a
    | +-comm c (a + b)
    | +-comm b (suc c)
    | +-comm a (suc (suc (c + b)))
    | +-comm c b
    | +-comm (b + c) a 
    | +-asso a b c = refl

+-rear : ∀ (a b c d : ℕ) → a + b + (c + d) ≡ a + (b + c) + d
+-rear zero b c d rewrite +-asso b c d = refl
+-rear (suc a) b c d
    rewrite (+-asso (suc a) b (c + d))
    | +-asso a (b + c) d
    | +-asso b c d = refl

+-swap : ∀ (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
+-swap a b c
    rewrite (+-comm a (b + c))
    | +-comm b (a + c)
    | +-asso a c b
    | +-comm c b
    | +-comm a (b + c) = refl

_*_ : ℕ → ℕ → ℕ
infixl 7 _*_
zero * b = zero
suc a * b = b + a * b

{-# BUILTIN NATTIMES _*_ #-}

*-id : ∀ (a : ℕ) → a * (suc zero) ≡ (suc zero) * a
*-id zero = refl
*-id (suc a)
    rewrite +-comm (suc zero) a
    | *-id a = refl

*-z : ∀ (a : ℕ) → a * zero ≡ zero * a
*-z zero = refl
*-z (suc a) rewrite *-z a = refl

*-comm : ∀ (a b : ℕ) → a * b ≡ b * a
*-comm zero b rewrite *-z b = refl
*-comm (suc a) zero rewrite *-z a = refl
*-comm (suc a) (suc b)
    rewrite (*-comm a (suc b))
    | (*-comm b (suc a))
    | (*-comm a b )
    | (+-comm b (a + b * a))
    | (+-comm a (b + b * a))
    | (+-comm a (b * a))
    | (+-comm b (b * a))
    | (+-asso (b * a) a b)
    | (+-asso (b * a) b a)
    | (+-comm a b) = refl

*-+-dist-r : ∀ (a b c : ℕ) → (a + b) * c ≡ a * c + b * c
*-+-dist-r zero b c = refl
*-+-dist-r (suc a) zero c
    rewrite (+-comm (suc a) zero)
    | +-comm a zero
    | +-asso c (a * c) zero
    | +-comm (a * c) zero = refl
*-+-dist-r (suc a) (suc b) c
    rewrite (+-comm a (suc b))
    | +-rear c (a * c) c (b * c)
    | +-comm (a * c) c
    | +-asso c (c + a * c) (b * c)
    | +-asso c (a * c) (b * c)
    | +-comm (a * c) (b * c)
    | *-+-dist-r b a c = refl

*-+-dist-l : ∀ (a b c : ℕ) → a * (b + c) ≡ a * b + a * c
*-+-dist-l a zero c rewrite (*-z a) = refl
*-+-dist-l a (suc b) zero
    rewrite (+-comm (suc b) zero)
    | *-z a
    | +-comm (a * suc b) zero = refl
*-+-dist-l a (suc b) (suc c)
    rewrite (+-comm b (suc c))
    | *-comm a (suc (suc (c + b)))
    | *-comm a (suc b)
    | *-comm a (suc c)
    | +-rear a (b * a) a (c * a)
    | +-comm (b * a) a
    | +-asso a (a + b * a) (c * a)
    | +-asso a (b * a) (c * a)
    | +-comm (b * a) (c * a)
    | *-comm (c + b) a
    | *-comm c a
    | *-comm b a
    | *-+-dist-l a c b = refl

*-asso : ∀ (a b c : ℕ) → a * b * c ≡ a * (b * c)
*-asso zero b c = refl
*-asso (suc a) zero c rewrite (*-asso a zero c) = refl
*-asso (suc a) (suc b) c
    rewrite (*-+-dist-r (suc b) (a * suc b) c)
    | *-asso a (suc b) c = refl

_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ (suc n) = m * (m ^ n)

^-dist-+-*-l : ∀ (a b c : ℕ) →  a ^ (b + c) ≡ (a ^ b) * (a ^ c)
^-dist-+-*-l a zero c
    rewrite (+-comm zero (a ^ c))
    | +-asso (a ^ c) zero zero = refl
^-dist-+-*-l a (suc b) c
    rewrite *-asso a (a ^ b) (a ^ c)
    | ^-dist-+-*-l a b c = refl

^-dist-*-r : ∀ (a b c : ℕ) → (a * b) ^ c ≡ (a ^ c) * (b ^ c)
^-dist-*-r a b zero rewrite (+-comm (suc zero) zero) = refl
^-dist-*-r a b (suc c)
    rewrite (*-asso a (a ^ c) (b * (b ^ c)))
    | *-comm (a ^ c) (b * (b ^ c))
    | *-asso b (b ^ c) (a ^ c)
    | *-comm (b ^ c) (a ^ c)
    | *-asso a b ((a * b) ^ c)
    | ^-dist-*-r a b c = refl

^-asso-* : ∀ (a b c : ℕ) → (a ^ b) ^ c ≡ a ^ (b * c)
^-asso-* a b zero rewrite (*-comm b zero) = refl
^-asso-* a b (suc c)
    rewrite (*-comm b (suc c))
    | ^-dist-+-*-l a b (c * b)
    | *-comm c b
    | ^-asso-* a b c = refl

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
from (n O) = 2 * (from n)
from (n I) = suc (2 * (from n))

thm₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
thm₁ ⟨⟩ = refl
thm₁ (a O) = refl
thm₁ (a I)
    rewrite thm₁ a
    | +-comm (suc (from a)) zero
    | +-comm (from a) zero
    | +-comm (from a) (suc (from a)) = refl

-- thm₂ : ∀ (b : Bin) → to (from b) = b
-- 这是错误的，因为 Bin 中的 (⟨⟩ O) 和 (⟨⟩)
-- 都和 自然数 的 0 对应
-- from 并非单射

thm₃ : ∀ (n : ℕ) → from (to n) ≡ n
thm₃ zero = refl
thm₃ (suc n)
  rewrite thm₁ (to (suc n))
    | thm₁ (to n)
    | thm₃ n = refl