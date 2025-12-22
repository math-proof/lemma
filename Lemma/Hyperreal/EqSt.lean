import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.Infinitesimal0
open Hyperreal


@[main]
private lemma main
-- given
  (r : ℝ) :
-- imply
  st r = r := by
-- proof
  apply EqSt.of.InfinitesimalSub
  simp
  apply Infinitesimal0


-- created on 2025-12-11
-- updated on 2025-12-12
