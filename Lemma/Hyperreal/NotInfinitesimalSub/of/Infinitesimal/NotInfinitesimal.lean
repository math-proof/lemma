import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalSub.is.InfinitesimalSub
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : ¬Infinitesimal b) :
-- imply
  ¬Infinitesimal (a - b) := by
-- proof
  contrapose! h_b
  have h_b := InfinitesimalSub.of.InfinitesimalSub h_b
  have := InfinitesimalAdd.of.Infinitesimal.Infinitesimal h_a h_b
  simp at this
  assumption


-- created on 2025-12-10
