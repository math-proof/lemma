import Lemma.Nat.AddMul.lt.Mul
open Nat


@[main]
private lemma main
-- given
  (h : i < m)
  (j : Fin n) :
-- imply
  i * n + j < m * n := by
-- proof
  let i : Fin m := ⟨i, h⟩
  have := AddMul.lt.Mul i j
  simp_all
  assumption


-- created on 2025-05-31
