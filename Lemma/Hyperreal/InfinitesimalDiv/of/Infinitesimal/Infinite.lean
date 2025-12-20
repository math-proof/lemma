import Lemma.Hyperreal.InfinitesimalDiv.of.NotInfinite.Infinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
open Hyperreal


@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : Infinite b) :
-- imply
  Infinitesimal (a / b) := by
-- proof
  apply InfinitesimalDiv.of.NotInfinite.Infinite _ h_b
  apply NotInfinite.of.Infinitesimal h_a


-- created on 2025-12-20
