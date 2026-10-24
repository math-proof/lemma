import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTailPower
open StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul_pow_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTailPower.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul_pow_pred_eq
  {R : FKRectTorus}
  {mu : ConfigSpace (Sym2 R.Vertex) → Real}
  {n : Nat}
  {a : Real}
-- given
  (hmu : ∀ rho, 0 ≤ mu rho)
  (hn : 0 < n)
  (hmass : ∀ (S : Finset (Fin R.width)), S.card = n → ∀ (pair : Fin R.width → Fin R.width) (first : Fin R.width), first ∈ S → StatMech.Probability.finiteEventMass mu {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} ≤ a ^ (S.erase first).card) :
-- imply
  StatMech.Probability.finiteEventMass mu {rho | n ≤ fkRectHorizontalCylinderCrossingClusterCount R rho} ≤ Nat.choose R.width n * R.width ^ R.width * a ^ (n - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul_pow_pred R mu hmu n hn a hmass


-- created on 2026-10-23
