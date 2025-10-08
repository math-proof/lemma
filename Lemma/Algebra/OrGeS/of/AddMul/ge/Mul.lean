import Lemma.Nat.AddMul.lt.Mul
open Nat


@[main]
private lemma main
  {i j : ℕ}
-- given
  (h : i * n + j ≥ m * n) :
-- imply
  i ≥ m ∨ j ≥ n := by
-- proof
  by_contra h
  simp at h
  let ⟨hi, hj⟩ := h
  let i' : Fin m := ⟨i, hi⟩
  let j' : Fin n := ⟨j, hj⟩
  have := AddMul.lt.Mul i' j'
  linarith [this, hi, hj]


-- created on 2025-05-09
