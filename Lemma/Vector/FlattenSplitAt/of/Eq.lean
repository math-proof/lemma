import Def.Data.Vector.Basic.Part2
import Lemma.Vector.EqFlattenUnflatten
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
open Vector Bool


@[path]
private lemma main
  {s s' : List ℕ}
  {a : List.Vector α s.prod}
  {b : List.Vector α s'.prod}
-- given
  (h : a ≃ b)
  (d : ℕ) :
-- imply
  (a.splitAt d).flatten ≃ (b.splitAt d).flatten := by
-- proof
  simp [SEq] at h ⊢
  unfold List.Vector.splitAt
  simp [EqFlattenUnflatten]
  simp_all


-- created on 2025-07-15
-- updated on 2026-11-20
