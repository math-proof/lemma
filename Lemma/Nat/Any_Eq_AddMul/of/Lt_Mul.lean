import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
open Nat


@[main]
private lemma fin
  {m n : ℕ}
-- given
  (h : t < m * n) :
-- imply
  ∃ (i : Fin m) (j : Fin n), t = i * n + j := by
-- proof
  have := Any_EqAddMul.of.Lt_Mul h
  aesop


@[main]
private lemma main
  {m n : ℕ}
-- given
  (h : t < m * n) :
-- imply
  ∃ i < m, ∃ j < n, t = i * n + j := by
-- proof
  have := fin h
  aesop


-- created on 2025-06-13
-- updated on 2025-10-22
