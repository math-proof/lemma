import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.InfinitesimalMul.of.NotInfinite.Infinitesimal
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


/--
the hypotheses are arranged in the constructor order of division a / b
-/
@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinite a)
  (h_b : Infinite b) :
-- imply
  Infinitesimal (a / b) := by
-- proof
  rw [Div.eq.Mul_Inv]
  apply InfinitesimalMul.of.NotInfinite.Infinitesimal h_a
  apply InfinitesimalInv.of.Infinite h_b


-- created on 2025-12-20
