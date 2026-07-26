import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Nat.Mul
open Hyperreal Nat


/--
the hypotheses are arranged in the constructor order of multiplication a * b
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.InfinitesimalMul.of.NotInfinite.Infinitesimal |
| mt 1 | Hyperreal.Infinite.of.NotInfinitesimalMul.Infinitesimal |
-/
@[main, mt 1]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬a → ∞)
  (h_b : b → 0) :
-- imply
  (a * b) → 0 := by
-- proof
  rw [Mul.comm]
  apply InfinitesimalMul.of.Infinitesimal.NotInfinite h_b h_a


-- created on 2025-12-20
