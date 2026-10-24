import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.OrderTransition
open MeasureTheory StatMech StatMech.FK


/--
[fkThetaFree_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean)
-/
@[path]
private lemma fkThetaFree_nonneg_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ fkThetaFree d hp hp1 hq (q := q) := by
-- proof
  apply StatMech.FK.fkThetaFree_nonneg d hp hp1 hq

/--
[fkThetaFree_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean)
-/
@[path]
private lemma fkThetaFree_le_one_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkThetaFree d hp hp1 hq (q := q) ≤ 1 := by
-- proof
  apply StatMech.FK.fkThetaFree_le_one d hp hp1 hq

/--
[firstOrderTransition_of_contour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean)
-/
@[path]
private lemma firstOrderTransition_of_contour_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hFree : fkThetaFree d hp hp1 hq (q := q) = 0)
  (hWired : 0 < fkTheta d hp hp1 hq (q := q)) :
-- imply
  IsFirstOrderTransition d hp hp1 hq := by
-- proof
  apply StatMech.FK.firstOrderTransition_of_contour d hp hp1 hq hFree hWired

/--
[fkThetaFree_ne_fkTheta_of_firstOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean)
-/
@[path]
private lemma fkThetaFree_ne_fkTheta_of_firstOrder_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (h : IsFirstOrderTransition d hp hp1 hq) :
-- imply
  fkThetaFree d hp hp1 hq (q := q) ≠ fkTheta d hp hp1 hq (q := q) := by
-- proof
  apply StatMech.FK.fkThetaFree_ne_fkTheta_of_firstOrder d hp hp1 hq h

/--
[freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean)
-/
@[path]
private lemma freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (h : IsFirstOrderTransition d hp hp1 hq) :
-- imply
  freeInfiniteVolume d hp hp1 hq ≠ wiredInfiniteVolume d hp hp1 hq := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder d hp hp1 hq h

/--
[order_transition_q_large](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean)
-/
@[path]
private lemma order_transition_q_large_eq
  {q : ℝ}
-- given
  (hq : 4 < q)
  (hpos : 0 < BeffaraDC.selfDualPoint q)
  (hlt : BeffaraDC.selfDualPoint q < 1)
  (hFree : fkThetaFree 2 hpos hlt (by linarith : (0 : ℝ) < q) (q := q) = 0)
  (hWired : 0 < fkTheta 2 hpos hlt (by linarith : (0 : ℝ) < q) (q := q)) :
-- imply
  IsFirstOrderTransition 2 hpos hlt (by linarith : (0 : ℝ) < q) ∧ freeInfiniteVolume 2 hpos hlt (by linarith : (0 : ℝ) < q) ≠ wiredInfiniteVolume 2 hpos hlt (by linarith : (0 : ℝ) < q) := by
-- proof
  apply StatMech.FK.order_transition_q_large hq hpos hlt hFree hWired

/--
[order_transition_q_large_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean)
-/
@[path]
private lemma order_transition_q_large_selfDual_eq
  {q : ℝ}
-- given
  (hq : 4 < q)
  (hFree : fkThetaFree 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2 (by linarith : (0 : ℝ) < q) (q := q) = 0)
  (hWired : 0 < fkTheta 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2 (by linarith : (0 : ℝ) < q) (q := q)) :
-- imply
  IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2 (by linarith : (0 : ℝ) < q) ∧ freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2 (by linarith : (0 : ℝ) < q) ≠ wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2 (by linarith : (0 : ℝ) < q) := by
-- proof
  apply StatMech.FK.order_transition_q_large_selfDual hq hFree hWired


-- created on 2026-10-23
