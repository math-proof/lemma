import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.NotInfinite
import Lemma.Rat.EqMul_Div.of.Ne_0
open Hyperreal Rat


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.of.InfiniteDiv.NotInfinitesimal |
| mt | Hyperreal.NotInfiniteDiv.of.NotInfinite.NotInfinitesimal |
-/
@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : Infinite (b / a)) :
-- imply
  Infinite b := by
-- proof
  if h_a_0 : a = 0 then
    subst h_a_0
    simp_all
    have := NotInfinite 0
    contradiction
  else
    have h_b := Hyperreal.InfiniteMul.of.Infinite.NotInfinitesimal h_b h_a
    rwa [EqMulDiv.of.Ne_0 h_a_0] at h_b


-- created on 2025-12-20
