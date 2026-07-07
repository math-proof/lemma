import Lemma.Hyperreal.StInv.eq.InvSt
import Lemma.Rat.InvDiv.eq.Div
open Hyperreal Rat


@[main, comm]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  stdPart (a / b) = (stdPart (b / a))⁻¹ := by
-- proof
  have := StInv.eq.InvSt (b / a)
  rwa [InvDiv.eq.Div] at this


-- created on 2025-12-10
