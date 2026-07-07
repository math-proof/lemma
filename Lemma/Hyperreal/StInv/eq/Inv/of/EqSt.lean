import Lemma.Hyperreal.StInv.eq.InvSt
open Hyperreal


@[main]
private lemma main
  [LinearOrder K] [Field K] [IsOrderedRing K]
  {x : K}
  {a : ℝ}
-- given
  (h : stdPart x = a) :
-- imply
  stdPart x⁻¹ = a⁻¹ := by
-- proof
  rw [StInv.eq.InvSt]
  rw [h]


-- created on 2025-12-08
-- updated on 2025-12-09
