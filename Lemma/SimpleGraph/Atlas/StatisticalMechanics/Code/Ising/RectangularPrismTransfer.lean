import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
open Finset Matrix Filter Topology StatMech StatMech.Ising


/--
[rectangularPrismLayer_equiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismLayer_equiv_symm_eq
  {m n h : Nat}
  {z : Fin (2 * h + 1)}
-- given
  (q : Fin (2 * h + 1) -> RectangularLayerConfig m n) :
-- imply
  rectangularPrismLayer ((rectangularPrismLayerEquiv m n h).symm q) z = q z := by
-- proof
  apply StatMech.Ising.rectangularPrismLayer_equiv_symm q z

/--
[sum_rectangularPrismSite_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma sum_rectangularPrismSite_eq_eq
  {m n h : Nat}
-- given
  (f : RectangularPrismSite m n h -> Real) :
-- imply
  (∑ v, f v) = ∑ x : Fin m, ∑ y : Fin n, ∑ z : Fin (2 * h + 1), f ⟨x, y, z⟩ := by
-- proof
  apply StatMech.Ising.sum_rectangularPrismSite_eq f

/--
[sum_comm_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma sum_comm_three_eq
  [Fintype A]
  [Fintype B]
  [Fintype C]
  [AddCommMonoid R]
-- given
  (f : A -> B -> C -> R) :
-- imply
  (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
-- proof
  apply StatMech.Ising.sum_comm_three f

/--
[mul_mul_fintype_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma mul_mul_fintype_sum_eq
  [Fintype A]
  {a b : Real}
-- given
  (f : A -> Real) :
-- imply
  a * b * (∑ x, f x) = ∑ x, a * b * f x := by
-- proof
  apply StatMech.Ising.mul_mul_fintype_sum a b f

/--
[rectangularPrismSpin_layer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismSpin_layer_eq
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h}
  {x : Fin m}
  {y : Fin n}
  {z : Fin (2 * h + 1)} :
-- imply
  rectangularPrismSpin sigma x y z = spin (rectangularPrismLayer sigma z) (x, y) := by
-- proof
  apply StatMech.Ising.rectangularPrismSpin_layer sigma x y z

/--
[rectangularPrismInternalInteraction_eq_layers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismInternalInteraction_eq_layers_eq
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  rectangularPrismInternalInteraction sigma = (∑ z : Fin (2 * h + 1), rectangularLayerInternalInteraction (rectangularPrismLayer sigma z)) + ∑ z : Fin (2 * h), ∑ p : Fin m × Fin n, spin (rectangularPrismLayer sigma z.castSucc) p * spin (rectangularPrismLayer sigma z.succ) p := by
-- proof
  apply StatMech.Ising.rectangularPrismInternalInteraction_eq_layers sigma

/--
[rectangularPrismBoundaryDegree_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismBoundaryDegree_split_eq
  {m n h : Nat}
  {x : Fin m}
  {y : Fin n}
  {z : Fin (2 * h + 1)} :
-- imply
  rectangularPrismBoundaryDegree ⟨x, y, z⟩ = rectangularLayerBoundaryDegree (x, y) + (if z.val = 0 then 1 else 0) + (if z.val + 1 = 2 * h + 1 then 1 else 0) := by
-- proof
  apply StatMech.Ising.rectangularPrismBoundaryDegree_split x y z

/--
[rectangularPrismPlusBoundaryInteraction_eq_layers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusBoundaryInteraction_eq_layers_eq
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  rectangularPrismPlusBoundaryInteraction sigma = (∑ z : Fin (2 * h + 1), ∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin (rectangularPrismLayer sigma z) p) + (∑ p : Fin m × Fin n, spin (rectangularPrismLayer sigma 0) p) + ∑ p : Fin m × Fin n, spin (rectangularPrismLayer sigma (Fin.last (2 * h))) p := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusBoundaryInteraction_eq_layers sigma

/--
[rectangularPrismPlusExponent_eq_layers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusExponent_eq_layers_eq
  {J beta : Real}
  {m n h : Nat}
  {sigma : RectangularPrismConfig m n h} :
-- imply
  -beta * rectangularPrismPlusEnergy J sigma = rectangularLayerFaceBoundary J beta (rectangularPrismLayer sigma 0) + rectangularLayerFaceBoundary J beta (rectangularPrismLayer sigma (Fin.last (2 * h))) + (∑ z : Fin (2 * h + 1), rectangularLayerBoltzmannInteraction J beta (rectangularPrismLayer sigma z)) + ∑ z : Fin (2 * h), rectangularLayerVerticalInteraction J beta (rectangularPrismLayer sigma z.castSucc) (rectangularPrismLayer sigma z.succ) := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusExponent_eq_layers J beta sigma

/--
[rectangularPrismTransfer_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismTransfer_isHermitian_eq
  {J beta : Real}
  {m n : Nat} :
-- imply
  (rectangularPrismTransfer J beta m n).IsHermitian := by
-- proof
  apply StatMech.Ising.rectangularPrismTransfer_isHermitian J beta m n

/--
[rectangularPrismTransfer_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismTransfer_pos_eq
  {J beta : Real}
  {m n : Nat}
  {s t : RectangularLayerConfig m n} :
-- imply
  0 < rectangularPrismTransfer J beta m n s t := by
-- proof
  apply StatMech.Ising.rectangularPrismTransfer_pos J beta m n s t

/--
[rectangularPrismTransferBoundaryVector_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismTransferBoundaryVector_pos_eq
  {J beta : Real}
  {m n : Nat}
  {s : RectangularLayerConfig m n} :
-- imply
  0 < rectangularPrismTransferBoundaryVector J beta m n s := by
-- proof
  apply StatMech.Ising.rectangularPrismTransferBoundaryVector_pos J beta m n s

/--
[rectangularPrismTransferPathWeight_eq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismTransferPathWeight_eq_exp_eq
  {J beta : Real}
-- given
  (m n h : Nat)
  (q : Fin (2 * h + 1) -> RectangularLayerConfig m n) :
-- imply
  rectangularPrismTransferBoundaryVector J beta m n (q 0) * (∏ z : Fin (2 * h), rectangularPrismTransfer J beta m n (q z.castSucc) (q z.succ)) * rectangularPrismTransferBoundaryVector J beta m n (q (Fin.last (2 * h))) = Real.exp (rectangularLayerFaceBoundary J beta (q 0) + rectangularLayerFaceBoundary J beta (q (Fin.last (2 * h))) + (∑ z : Fin (2 * h + 1), rectangularLayerBoltzmannInteraction J beta (q z)) + ∑ z : Fin (2 * h), rectangularLayerVerticalInteraction J beta (q z.castSucc) (q z.succ)) := by
-- proof
  apply StatMech.Ising.rectangularPrismTransferPathWeight_eq_exp J beta m n h q

/--
[rectangularPrismTransferPartition_eq_sum_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismTransferPartition_eq_sum_path_eq
  {J beta : Real}
-- given
  (m n h : Nat) :
-- imply
  rectangularPrismTransferPartition J beta m n h = ∑ q : Fin (2 * h + 1) -> RectangularLayerConfig m n, Real.exp (rectangularLayerFaceBoundary J beta (q 0) + rectangularLayerFaceBoundary J beta (q (Fin.last (2 * h))) + (∑ z : Fin (2 * h + 1), rectangularLayerBoltzmannInteraction J beta (q z)) + ∑ z : Fin (2 * h), rectangularLayerVerticalInteraction J beta (q z.castSucc) (q z.succ)) := by
-- proof
  apply StatMech.Ising.rectangularPrismTransferPartition_eq_sum_path J beta m n h

/--
[rectangularPrismPlusPartition_eq_transferPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusPartition_eq_transferPartition_eq
  {J beta : Real}
-- given
  (m n h : Nat) :
-- imply
  rectangularPrismPlusPartition J beta m n h = rectangularPrismTransferPartition J beta m n h := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusPartition_eq_transferPartition J beta m n h

/--
[rectangularPrismPlusPartition_eq_centerDenominator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusPartition_eq_centerDenominator_eq
  {J beta : Real}
-- given
  (m n h : Nat) :
-- imply
  rectangularPrismPlusPartition J beta m n h = ∑ s, (((rectangularPrismTransfer J beta m n) ^ h) *ᵥ rectangularPrismTransferBoundaryVector J beta m n) s ^ 2 := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusPartition_eq_centerDenominator J beta m n h

/--
[rectangularPrismPlusCentralSpinNumerator_eq_markedPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusCentralSpinNumerator_eq_markedPath_eq
  {J beta : Real}
  {p : Fin m × Fin n}
-- given
  (m n h : Nat) :
-- imply
  rectangularPrismPlusCentralSpinNumerator J beta m n h p = centerMarkedPathSum (rectangularPrismTransfer J beta m n) (rectangularPrismTransferBoundaryVector J beta m n) (fun s => spin s p) h := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusCentralSpinNumerator_eq_markedPath J beta m n h p

/--
[rectangularPrismPlusCentralSpinNumerator_eq_transferSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusCentralSpinNumerator_eq_transferSquare_eq
  {J beta : Real}
  {p : Fin m × Fin n}
-- given
  (m n h : Nat) :
-- imply
  rectangularPrismPlusCentralSpinNumerator J beta m n h p = ∑ s, spin s p * (((rectangularPrismTransfer J beta m n) ^ h) *ᵥ rectangularPrismTransferBoundaryVector J beta m n) s ^ 2 := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusCentralSpinNumerator_eq_transferSquare J beta m n h p

/--
[rectangularPrismPlusPartition_log_div_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusPartition_log_div_tendsto_eq
  {J beta : Real}
  {m n : Nat} :
-- imply
  ∃ lam : Real, 0 < lam ∧ Tendsto (fun h : Nat => Real.log (rectangularPrismPlusPartition J beta m n h) / (2 * h : Real)) atTop (nhds (Real.log lam)) := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusPartition_log_div_tendsto J beta m n

/--
[rectangularPrismPlusCentralSpinMean_eq_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusCentralSpinMean_eq_transfer_eq
  {J beta : Real}
  {m n : Nat}
  {p : Fin m × Fin n}
-- given
  (h : Nat) :
-- imply
  rectangularPrismPlusCentralSpinMean J beta m n p h = rectangularPrismCenterSpinMean J beta m n p h := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusCentralSpinMean_eq_transfer J beta m n p h

/--
[rectangularPrismCenterSpinMean_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismCenterSpinMean_tendsto_eq
  {J beta : Real}
  {m n : Nat}
  {p : Fin m × Fin n} :
-- imply
  ∃ m0 : Real, Tendsto (rectangularPrismCenterSpinMean J beta m n p) atTop (nhds m0) := by
-- proof
  apply StatMech.Ising.rectangularPrismCenterSpinMean_tendsto J beta m n p

/--
[rectangularPrismPlusCentralSpinMean_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean)
-/
@[path]
private lemma rectangularPrismPlusCentralSpinMean_tendsto_eq
  {J beta : Real}
  {m n : Nat}
  {p : Fin m × Fin n} :
-- imply
  ∃ m0 : Real, Tendsto (rectangularPrismPlusCentralSpinMean J beta m n p) atTop (nhds m0) := by
-- proof
  apply StatMech.Ising.rectangularPrismPlusCentralSpinMean_tendsto J beta m n p


-- created on 2026-10-23
