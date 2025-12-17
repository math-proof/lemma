import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : Infinite x) :
-- imply
  ¬x⁻¹.Infinite := by
-- proof
  apply NotInfiniteInv.of.NotInfinitesimal
  apply NotInfinitesimal.of.Infinite h


-- created on 2025-12-17
