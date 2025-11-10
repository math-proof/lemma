import Lemma.List.EqLengthSlice_Mul.of.Lt
open List


@[main]
private lemma main
  {i : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  (⟨i, (m * n : ℕ), n⟩ : Slice).length (m * n) = m := by
-- proof
  apply EqLengthSlice_Mul.of.Lt h m


-- created on 2025-11-09
