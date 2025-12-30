import Lemma.Tensor.Setoid.is.SetoidDataS
import Lemma.Vector.SetoidExpS.of.Setoid_0
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
  apply Setoid.of.SetoidDataS
  simp
  have h := SetoidDataS.of.Setoid h
  have := SetoidExpS.of.Setoid_0 h
  rwa [exp] at this


-- created on 2025-12-24
