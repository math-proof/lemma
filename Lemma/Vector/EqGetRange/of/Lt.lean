import Lemma.Vector.EqGetRange
open Vector


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : i < n) :
-- imply
  (List.Vector.range n)[i] = i := by
-- proof
  let i' : Fin n := ⟨i, h⟩
  have : i' = i := rfl
  have := EqGetRange i'
  simp_all


-- created on 2025-06-03
