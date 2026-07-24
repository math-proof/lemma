import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.XEqExpS.of.XEq_0
open Tensor Vector


@[main]
private lemma main
  {X Y : Tensor ℝ* s}
-- given
  (h : X - Y ≈ 0) :
-- imply
  exp X ≈ exp Y := by
-- proof
  simp [exp]
  apply XEq.of.XEqDataS
  simp
  have h := XEqDataS.of.XEq h
  have := XEqExpS.of.XEq_0 h
  rwa [exp] at this


-- created on 2025-12-24
