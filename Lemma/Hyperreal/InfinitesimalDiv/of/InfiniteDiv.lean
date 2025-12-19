import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
open Hyperreal


@[main]
private lemma main
-- given
  (h : Infinite (a / b)) :
-- imply
  Infinitesimal (b / a) := by
-- proof
  have := InfinitesimalInv.of.Infinite h
  simp at this
  assumption


-- created on 2025-12-11
