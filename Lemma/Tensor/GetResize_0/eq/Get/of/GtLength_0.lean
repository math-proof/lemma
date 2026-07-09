import Lemma.Bool.SEqCast.of.Eq
import Lemma.Tensor.SEqResize_0.of.GtLength_0
open Bool Tensor List Nat Vector


@[main, cast]
private lemma main
  [Zero α]
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  (X.resize ⟨0, by grind⟩)[i] ≃ X[i] := by
-- proof
  simp [GetElem.getElem]
  rw [Resize_0.eq.Cast.of.GtLength_0 h]

  apply SEqCast.of.Eq
  simp


-- created on 2026-07-09
