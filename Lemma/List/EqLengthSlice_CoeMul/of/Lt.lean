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


@[main]
private lemma comm'
  {i : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  (⟨i, (n * m : ℕ), n⟩ : Slice).length (n * m) = m := by
-- proof
  apply EqLengthSlice_Mul.of.Lt.comm h m


-- created on 2025-11-09
