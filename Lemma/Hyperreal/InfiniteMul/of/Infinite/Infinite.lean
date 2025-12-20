import Lemma.Hyperreal.InfiniteMul.of.Infinite.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinite a)
  (h_b : Infinite b) :
-- imply
  Infinite (a * b) := by
-- proof
  apply InfiniteMul.of.Infinite.NotInfinitesimal h_a
  apply NotInfinitesimal.of.Infinite h_b


-- created on 2025-12-16
-- updated on 2025-12-20
