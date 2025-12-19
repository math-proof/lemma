import Lemma.Hyperreal.Infinite.of.Infinite.StDiv.ne.Zero
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.StDiv.ne.Zero
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.NotInfiniteInv.of.Infinite
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_st : st (a / b) = 1)
  (h_a : ¬a.Infinitesimal) :
-- imply
  ¬(a * b)⁻¹.Infinite := by
-- proof
  if h_a_inf : a.Infinite then
    apply NotInfiniteInv.of.Infinite
    apply InfiniteMul.of.Infinite.Infinite h_a_inf
    apply Infinite.of.Infinite.StDiv.ne.Zero.left (by linarith) h_a_inf
  else
    apply NotInfiniteInv.of.NotInfinitesimal
    apply NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a
    apply NotInfinitesimal.of.NotInfinitesimal.StDiv.ne.Zero (by linarith) h_a


-- created on 2025-12-18
