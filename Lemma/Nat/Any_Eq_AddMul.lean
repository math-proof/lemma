import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
open Fin


@[main]
private lemma main
  {m n : ℕ}
-- given
  (t : Fin (m * n)) :
-- imply
  ∃ i : Fin m, ∃ j : Fin n, t = i.val * n + j := by
-- proof
  let ⟨t, h_t⟩ := t
  obtain ⟨i, j, h_eq⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  use i, j


@[main]
private lemma Comm
  {m n : ℕ}
-- given
  (t : Fin (m * n)) :
-- imply
  ∃ i : Fin m, ∃ j : Fin n, t = n * i + j := by
-- proof
  simp [mul_comm (a := n)]
  apply main

-- created on 2025-07-03
