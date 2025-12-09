import Mathlib.Analysis.Real.Hyperreal
import Lemma.Hyperreal.StInv.eq.InvSt
open Hyperreal


@[main]
private lemma main
-- given
  (h : st x = a) :
-- imply
  st x⁻¹ = a⁻¹ := by
-- proof
  rw [StInv.eq.InvSt]
  rw [h]


-- created on 2025-12-08
-- updated on 2025-12-09
