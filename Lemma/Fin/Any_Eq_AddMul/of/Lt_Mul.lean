import Lemma.Nat.Any_EqAddMul.of.Lt_Mul
open Nat


@[main]
private lemma main
  {m n : ℕ}
-- given
  (h : t < m * n) :
-- imply
  ∃ (i : Fin m) (j : Fin n), t = i * n + j := by
-- proof
  have := Any_EqAddMul.of.Lt_Mul h
  aesop


-- created on 2025-12-01
