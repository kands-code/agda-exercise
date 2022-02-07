module Self where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

data B : Set where
  T : B
  F : B

_&&_ : B -> B -> B
infixl 20 _&&_
T && T = T
T && F = F
F && _ = F

_||_ : B -> B -> B
infixl 15 _||_
T || _ = T
F || T = T
F || F = F

p||p≡p : ∀ (p : B) -> p || p ≡ p
p||p≡p T = refl
p||p≡p F = refl

p&&p≡p : ∀ (p : B) -> p && p ≡ p
p&&p≡p T = refl
p&&p≡p F = refl

-- 交换律

a&&b≡b&&a : ∀ (a b : B) -> a && b ≡ b && a
a&&b≡b&&a T T = refl
a&&b≡b&&a T F = refl
a&&b≡b&&a F T = refl
a&&b≡b&&a F F = refl

a||b≡b||a : ∀ (a b : B) -> a || b ≡ b || a
a||b≡b||a T T = refl
a||b≡b||a T F = refl
a||b≡b||a F T = refl
a||b≡b||a F F = refl

abc||abc : ∀ (a b c : B) -> (a || b) || c ≡ a || (b || c)
abc||abc T b c = refl
abc||abc F T c = refl
abc||abc F F T = refl
abc||abc F F F = refl

abc&&abc : ∀ (a b c : B) -> a && b && c ≡ a && (b && c)
abc&&abc T T T = refl
abc&&abc T T F = refl
abc&&abc T F c = refl
abc&&abc F b c = refl

-- 分配律

a&&b||c≡a&&b||a&&c : ∀ (a b c : B) -> a && (b || c) ≡ a && b || a && c
a&&b||c≡a&&b||a&&c T T c = refl
a&&b||c≡a&&b||a&&c T F T = refl
a&&b||c≡a&&b||a&&c T F F = refl
a&&b||c≡a&&b||a&&c F T c = refl
a&&b||c≡a&&b||a&&c F F c = refl

a||b&&c≡a||b&&a||c : ∀ (a b c : B) -> a || b && c ≡ (a || b) && (a || c)
a||b&&c≡a||b&&a||c T b c = refl
a||b&&c≡a||b&&a||c F T T = refl
a||b&&c≡a||b&&a||c F T F = refl
a||b&&c≡a||b&&a||c F F c = refl

T&&p≡p : ∀ (p : B) -> T && p ≡ p
T&&p≡p T = refl
T&&p≡p F = refl

F||p≡p : ∀ (p : B) -> F || p ≡ p
F||p≡p T = refl
F||p≡p F = refl

¬_ : B -> B
infix 25 ¬_
¬ F = T
¬ T = F

-- 负负得正
¬¬p≡p : ∀ (p : B) -> ¬ (¬ p) ≡ p
¬¬p≡p T = refl
¬¬p≡p F = refl

-- 德·摩根律

¬a&&b≡¬a||¬b : ∀ (a b : B) -> ¬ (a && b) ≡ ¬ a || ¬ b
¬a&&b≡¬a||¬b T T = refl
¬a&&b≡¬a||¬b T F = refl
¬a&&b≡¬a||¬b F T = refl
¬a&&b≡¬a||¬b F F = refl

¬a||b≡¬a&&¬b : ∀ (a b : B) -> ¬ (a || b) ≡ ¬ a && ¬ b
¬a||b≡¬a&&¬b T T = refl
¬a||b≡¬a&&¬b T F = refl
¬a||b≡¬a&&¬b F T = refl
¬a||b≡¬a&&¬b F F = refl

-- 自反律

p&&¬p≡F : ∀ (p : B) -> p && ¬ p ≡ F
p&&¬p≡F T = refl
p&&¬p≡F F = refl

-- 排中律

¬p||p≡T : ∀ (p : B) -> ¬ p || p ≡ T
¬p||p≡T T = refl
¬p||p≡T F = refl

-- 蕴含 如果 .. 就

_to_ : B -> B -> B
infixl 10 _to_
T to F = F
T to T = T
F to _ = T

-- 蕴含等值推演
ptoq≡¬p||q : ∀ (p q : B) -> p to q ≡ ¬ p || q
ptoq≡¬p||q T T = refl
ptoq≡¬p||q T F = refl
ptoq≡¬p||q F q = refl

Ttop≡p : ∀ (p : B) -> T to p ≡ p
Ttop≡p T = refl
Ttop≡p F = refl

Ftop≡T : ∀ (p : B) -> F to p ≡ T
Ftop≡T p = refl

-- 等价

_<>_ : B -> B -> B
infixl 10 _eq_
T <> T = T
F <> T = F
T <> F = F
F <> F = T

-- 等价等值式
p<>q≡ptoq&&qtop : ∀ (p q : B) -> p <> q ≡ (p to q) && (q to p)
p<>q≡ptoq&&qtop T T = refl
p<>q≡ptoq&&qtop T F = refl
p<>q≡ptoq&&qtop F T = refl
p<>q≡ptoq&&qtop F F = refl

-- lemma 01

p||q&&¬q≡p : ∀ (p q : B) -> p || q && ¬ q ≡ p
p||q&&¬q≡p T T = refl
p||q&&¬q≡p T F = refl
p||q&&¬q≡p F q rewrite p&&¬p≡F q = refl

-- proof 01

p&&q||p&&¬q≡p : ∀ (p q : B) -> p && q || p && ¬ q ≡ p 
p&&q||p&&¬q≡p T T = refl
p&&q||p&&¬q≡p T F = refl
p&&q||p&&¬q≡p F q = refl

-- proof 02

atob≡¬bto¬a : ∀ (a b : B) -> a to b ≡ ¬ b to ¬ a
atob≡¬bto¬a a b
  rewrite ptoq≡¬p||q a b
    | ptoq≡¬p||q (¬ b) (¬ a)
    | a||b≡b||a (¬ a) b
    | ¬¬p≡p b = refl

implies₁ : ∀ (p q r s : B) -> ((p to (q to r)) && (¬ s || p) && q) to (s to r) ≡ T
implies₁ T T T T = refl
implies₁ T T T F = refl
implies₁ T T F s = refl
implies₁ T F T T = refl
implies₁ T F T F = refl
implies₁ T F F T = refl
implies₁ T F F F = refl
implies₁ F T T T = refl
implies₁ F T T F = refl
implies₁ F T F T = refl
implies₁ F T F F = refl
implies₁ F F r T = refl
implies₁ F F r F = refl
