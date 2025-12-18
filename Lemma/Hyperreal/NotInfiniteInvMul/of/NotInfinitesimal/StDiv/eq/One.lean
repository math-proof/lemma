import Lemma.Hyperreal.Infinite.of.Infinite.StDiv.ne.Zero
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.StDiv.ne.Zero
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.NotInfiniteInv.of.Infinite
import Lemma.Hyperreal.NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal
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
    have h_b_inf := Infinite.of.Infinite.StDiv.ne.Zero.left (by linarith) h_a_inf (b := b)
    have h_ab_inf := InfiniteMul.of.Infinite.Infinite h_a_inf h_b_inf
    exact NotInfiniteInv.of.Infinite h_ab_inf
  else
    have h_b := NotInfinitesimal.of.NotInfinitesimal.StDiv.ne.Zero (by linarith) h_a (b := b)
    have h_ab_ne_eps := NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a h_b
    exact NotInfiniteInv.of.NotInfinitesimal h_ab_ne_eps


-- created on 2025-12-18
