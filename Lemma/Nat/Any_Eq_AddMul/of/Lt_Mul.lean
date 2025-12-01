import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
open Fin


@[main]
private lemma main
  {m n : ℕ}
-- given
  (h : t < m * n) :
-- imply
  ∃ i < m, ∃ j < n, t = i * n + j := by
-- proof
  have := Any_Eq_AddMul.of.Lt_Mul h
  aesop


-- created on 2025-06-13
-- updated on 2025-12-01
