import Lemma.Algebra.EqGetValRange
open Algebra


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : i < n) :
-- imply
  have : i < (List.Vector.range n).val.length := by simpa [List.Vector.length]
  (List.Vector.range n).val[i] = ⟨i, h⟩ := by
-- proof
  let i' : Fin n := ⟨i, h⟩
  have : i' = i := rfl
  have := EqGetValRange i'
  simp_all
  simp [i']


-- created on 2025-07-05
