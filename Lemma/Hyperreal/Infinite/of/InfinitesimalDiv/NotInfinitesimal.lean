import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Rat.Div.eq.Mul_Inv
open Hyperreal Rat


/--
| attributes | lemma |
| :---: | :---: |
| path | Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal |
| mt   | Hyperreal.NotInfinitesimalDiv.of.NotInfinite.NotInfinitesimal |
| mt 1 | Hyperreal.Infinitesimal.of.InfinitesimalDiv.NotInfinite |
-/
@[path, mt, mt 1]
private lemma main
  [NeZero (b : ℝ*)]
  {a : ℝ*}
-- given
  (h_a : ¬a → 0)
  (h_b : (a / b) → 0) :
-- imply
  b → ∞ := by
-- proof
  contrapose! h_b
  rw [Div.eq.Mul_Inv]
  apply not_lt.mp
  apply NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a
  apply NotInfinitesimalInv.of.NotInfinite (not_lt.mpr h_b)


-- created on 2025-12-19
