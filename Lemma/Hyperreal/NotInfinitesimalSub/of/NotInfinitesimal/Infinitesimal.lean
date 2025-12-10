import Lemma.Hyperreal.InfinitesimalSub.is.InfinitesimalSub
import Lemma.Hyperreal.NotInfinitesimalSub.of.Infinitesimal.NotInfinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : Infinitesimal b) :
-- imply
  ¬Infinitesimal (a - b) := by
-- proof
  rw [InfinitesimalSub.is.InfinitesimalSub]
  apply NotInfinitesimalSub.of.Infinitesimal.NotInfinitesimal
  repeat assumption


-- created on 2025-12-10
