import Lemma.Hyperreal.StDiv.eq.InvStInv
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : st (b / a) = r) :
-- imply
  (a / b).st = r⁻¹ := by
-- proof
  rw [StDiv.eq.InvStInv]
  rw [h]


-- created on 2025-12-17
