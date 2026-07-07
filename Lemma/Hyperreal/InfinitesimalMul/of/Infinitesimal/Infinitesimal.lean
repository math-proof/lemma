import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : a → 0)
  (h_b : b → 0) :
-- imply
  (a * b) → 0 := by
-- proof
  apply InfinitesimalMul.of.Infinitesimal.NotInfinite h_a
  apply NotInfinite.of.Infinitesimal h_b


-- created on 2025-12-09
-- updated on 2025-12-20
