import Lemma.Hyperreal.InfiniteMul.of.NotInfinitesimal.Infinite
import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.NotInfinite
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


/--
the hypotheses are arranged in the constructor order of substraction a / b
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.InfiniteDiv.of.NotInfinitesimal.Infinitesimal |
| mt 1 | Hyperreal.Infinitesimal.of.NotInfiniteDiv.Infinitesimal |
-/
@[main, mt 1]
private lemma main
  {a : ℝ*}
  [NeZero (b : ℝ*)]
-- given
  (h_a : ¬a → 0)
  (h_b : b → 0) :
-- imply
  (a / b) → ∞ := by
-- proof
  rw [Div.eq.Mul_Inv]
  apply InfiniteMul.of.NotInfinitesimal.Infinite h_a
  apply InfiniteInv.of.Infinitesimal h_b


-- created on 2026-07-26
