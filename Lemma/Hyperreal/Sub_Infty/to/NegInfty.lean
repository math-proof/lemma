import Lemma.Hyperreal.Add_Infty.to.Infty
import Lemma.Hyperreal.SetoidNegS.of.Setoid
import Lemma.Nat.Sub.eq.AddNeg
open Hyperreal Nat


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  x - Hyperreal.omega ≈ -Hyperreal.omega := by
-- proof
  have := Add_Infty.to.Infty (-x)
  simp at this
  rw [AddNeg.eq.Sub] at this
  have := SetoidNegS.of.Setoid this
  aesop


-- created on 2025-12-23
