import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
import Lemma.Int.Sub.eq.Add_Neg
open Hyperreal Int


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : a → 0)
  (h_b : b → 0) :
-- imply
  (a - b) → 0:= by
-- proof
  rw [Sub.eq.Add_Neg]
  apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal h_a
  apply InfinitesimalNeg.of.Infinitesimal h_b


-- created on 2025-12-09
