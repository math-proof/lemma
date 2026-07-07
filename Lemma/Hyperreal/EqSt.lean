import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.Infinitesimal0
open Hyperreal


@[main]
private lemma main
-- given
  (r : ℝ) :
-- imply
  stdPart (r : ℝ*) = r := by
-- proof
  apply EqSt.of.InfinitesimalSub
  simp


-- created on 2025-12-11
-- updated on 2025-12-12
