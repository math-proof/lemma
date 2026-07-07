import Lemma.Hyperreal.StDiv.eq.InvStInv
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : stdPart (b / a) = r) :
-- imply
  stdPart (a / b) = r⁻¹ := by
-- proof
  rw [StDiv.eq.InvStInv]
  rw [h]


-- created on 2025-12-17
