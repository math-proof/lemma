import Lemma.Tensor.Select.eq.FromVectorMapToVector.of.GtLength
open Tensor


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : s.length > d)
  (i : Fin s[d])
  (X : Tensor α (n :: s)) :
-- imply
  X.select ⟨d + 1, by grind⟩ ⟨i, by grind⟩ = Tensor.fromVector (X.toVector.map (·.select ⟨d, by grind⟩ i)) := by
-- proof
  exact Select.eq.FromVectorMapToVector.of.GtLength h X i


-- created on 2025-11-15
-- updated on 2026-07-23
