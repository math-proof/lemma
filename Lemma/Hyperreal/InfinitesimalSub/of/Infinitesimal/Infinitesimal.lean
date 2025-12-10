import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
import Lemma.Int.Sub.eq.Add_Neg
open Hyperreal Int


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : Infinitesimal b) :
-- imply
  Infinitesimal (a - b) := by
-- proof
  rw [Sub.eq.Add_Neg]
  apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal h_a
  apply InfinitesimalNeg.of.Infinitesimal h_b


-- created on 2025-12-09
