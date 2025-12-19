import Lemma.Hyperreal.InfinitesimalPow.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : Infinitesimal x) :
-- imply
  Infinitesimal x² := 
-- proof
  InfinitesimalPow.of.Infinitesimal h


-- created on 2025-12-19
