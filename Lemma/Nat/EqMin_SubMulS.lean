import Lemma.Nat.Le_SubMulS
open Nat


@[main]
private lemma left
-- given
  (m n : ℕ)
  (i : Fin n) :
-- imply
  m ⊓ (m * n - m * i) = m := by
-- proof
  have := Le_SubMulS.left (n := n) (m := m) (i := i)
  simp [this]


@[main]
private lemma main
-- given
  (n m : ℕ)
  (i : Fin n) :
-- imply
  m ⊓ (n * m - i * m) = m := by
-- proof
  have := Le_SubMulS (n := n) (m := m) (i := i)
  simp [this]


-- created on 2025-05-07
-- updated on 2025-07-15
