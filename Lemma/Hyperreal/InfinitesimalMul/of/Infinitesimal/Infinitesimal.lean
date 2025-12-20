import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : Infinitesimal b) :
-- imply
  Infinitesimal (a * b) := by
-- proof
  apply InfinitesimalMul.of.Infinitesimal.NotInfinite h_a
  apply NotInfinite.of.Infinitesimal h_b


-- created on 2025-12-09
-- updated on 2025-12-20
