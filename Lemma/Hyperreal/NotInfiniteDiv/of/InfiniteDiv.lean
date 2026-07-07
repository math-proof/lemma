import Lemma.Hyperreal.InfinitesimalDiv.of.InfiniteDiv
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : (a / b) → ∞) :
-- imply
  ¬(b / a) → ∞ := by
-- proof
  apply NotInfinite.of.Infinitesimal
  apply InfinitesimalDiv.of.InfiniteDiv h


-- created on 2025-12-21
