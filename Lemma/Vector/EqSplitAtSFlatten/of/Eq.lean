import Lemma.Vector.EqFlattenUnflatten
import Lemma.Vector.EqValS.of.SEq
import Lemma.Logic.EqCastS.of.Eq.Eq.Eq
open Logic Vector


@[main]
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
  simp [SEq] at *
  unfold List.Vector.splitAt
  simp [EqFlattenUnflatten]
  simp_all

-- created on 2025-07-15
