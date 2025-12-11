import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : Infinitesimal x)
  (r : ℝ) :
-- imply
  Infinitesimal (x * r) := by
-- proof
  have := InfinitesimalDiv.of.Infinitesimal h r⁻¹
  simp at this
  assumption


-- created on 2025-12-11
