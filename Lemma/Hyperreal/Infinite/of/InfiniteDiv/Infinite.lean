import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.NotInfinite
import Lemma.Rat.EqMul_Div.of.Ne_0
open Hyperreal Rat


@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinite a)
  (h_b : Infinite (b / a)) :
-- imply
  Infinite b := by
-- proof
  if h_a_0 : a = 0 then
    subst h_a_0
    have := NotInfinite 0
    contradiction
  else
    have := InfiniteMul.of.Infinite.Infinite h_a h_b
    rwa [EqMul_Div.of.Ne_0 h_a_0] at this


-- created on 2025-12-20
