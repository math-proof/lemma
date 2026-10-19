import Lemma.List.EqLengthSlice_Mul
open Int Nat Rat List


@[path]
private lemma main
  {i : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  (⟨i, m * n, n⟩ : Slice).length (m * n) = m := by
-- proof
  have := EqLengthSlice_Mul ⟨i, h⟩ m
  simp_all


@[path]
private lemma Comm
  {i : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  (⟨i, n * m, n⟩ : Slice).length (n * m) = m := by
-- proof
  have := EqLengthSlice_Mul.comm ⟨i, h⟩ m
  simp_all


-- created on 2025-11-09
-- updated on 2025-11-14
