import sympy.core.power
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalPow
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x → 0) :
-- imply
  x² → 0 :=
-- proof
  InfinitesimalPow.of.Infinitesimal h


-- created on 2025-12-19
