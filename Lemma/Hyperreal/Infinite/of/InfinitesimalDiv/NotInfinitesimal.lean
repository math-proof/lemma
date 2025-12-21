import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal |
| mt   | Hyperreal.NotInfinitesimalDiv.of.NotInfinite.NotInfinitesimal |
| mt 1 | Hyperreal.Infinitesimal.of.InfinitesimalDiv.NotInfinite |
-/
@[main, mt, mt 1]
private lemma main
  [NeZero (b : ℝ*)]
  {a : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : Infinitesimal (a / b)) :
-- imply
  Infinite b := by
-- proof
  contrapose! h_b
  rw [Div.eq.Mul_Inv]
  apply NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a
  apply NotInfinitesimalInv.of.NotInfinite h_b


-- created on 2025-12-19
