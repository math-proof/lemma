import Lemma.List.EqLengthSlice_CoeMul.of.Lt
open List


@[main]
private lemma main
  {i : ℕ}
-- given
  (h : i < n) :
-- imply
  (⟨i, n, n⟩ : Slice).length n = 1 := by
-- proof
  have := EqLengthSlice_CoeMul.of.Lt h 1
  simpa


-- created on 2025-11-10
