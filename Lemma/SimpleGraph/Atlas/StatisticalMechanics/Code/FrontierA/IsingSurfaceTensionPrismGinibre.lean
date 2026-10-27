import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part7
open Finset MeasureTheory StatMech StatMech.FrontierA


/--
[oddPrismTouchToInternal_toTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismTouchToInternal_toTouch_eq
  {n : Nat}
  {q : OddPrismInternalIndex n} :
-- imply
  oddPrismTouchToInternal n (oddPrismInternalIndexToTouch n q) = some q := by
-- proof
  apply StatMech.FrontierA.oddPrismTouchToInternal_toTouch n q

/--
[oddPrismInternalIndexToTouch_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismInternalIndexToTouch_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (oddPrismInternalIndexToTouch n) := by
-- proof
  apply StatMech.FrontierA.oddPrismInternalIndexToTouch_injective n

/--
[oddPrismInternalEdge_map_eq_touch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismInternalEdge_map_eq_touch_eq
  {n : Nat}
  {q : OddPrismInternalIndex n} :
-- imply
  Sym2.map (fun v => (rectangularPrismSiteEquivSctBoxDobrushin n v).1) (oddPrismInternalEdge n q) = oddPrismTouchIndexBond n (oddPrismInternalIndexToTouch n q) := by
-- proof
  apply StatMech.FrontierA.oddPrismInternalEdge_map_eq_touch n q

/--
[oddPrismInternalEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismInternalEdge_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (oddPrismInternalEdge n) := by
-- proof
  apply StatMech.FrontierA.oddPrismInternalEdge_injective n

/--
[sum_oddPrismInternalEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma sum_oddPrismInternalEdges_eq
  {n : Nat}
-- given
  (f : Sym2 (RectangularPrismSite (2 * n + 1) (2 * n + 1) n) -> Real) :
-- imply
  (∑ e ∈ oddPrismInternalEdges n, f e) = ∑ q : OddPrismInternalIndex n, f (oddPrismInternalEdge n q) := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismInternalEdges n f

/--
[rectangularPrismInternalInteraction_eq_coordinateSums](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma rectangularPrismInternalInteraction_eq_coordinateSums_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  rectangularPrismInternalInteraction sigma = (∑ x : Fin (2 * n), ∑ y : Fin (2 * n + 1), ∑ z : Fin (2 * n + 1), rectangularPrismSpin sigma ⟨x.val, by omega⟩ y z * rectangularPrismSpin sigma ⟨x.val + 1, by omega⟩ y z) + (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n), ∑ z : Fin (2 * n + 1), rectangularPrismSpin sigma x ⟨y.val, by omega⟩ z * rectangularPrismSpin sigma x ⟨y.val + 1, by omega⟩ z) + (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1), ∑ z : Fin (2 * n), rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ * rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩) := by
-- proof
  apply StatMech.FrontierA.rectangularPrismInternalInteraction_eq_coordinateSums n sigma

/--
[sum_oddPrismInternalEdges_bond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma sum_oddPrismInternalEdges_bond_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  (∑ e ∈ oddPrismInternalEdges n, bond sigma e) = rectangularPrismInternalInteraction sigma := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismInternalEdges_bond n sigma

/--
[abs_oddPrismDobrushinField_le_plusField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma abs_oddPrismDobrushinField_le_plusField_eq
  {n : Nat}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  |oddPrismDobrushinField n v| <= oddPrismPlusField n v := by
-- proof
  apply StatMech.FrontierA.abs_oddPrismDobrushinField_le_plusField n v

/--
[sum_oddPrismPlusField_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma sum_oddPrismPlusField_spin_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  (∑ v, oddPrismPlusField n v * spin sigma v) = rectangularPrismPlusBoundaryInteraction sigma := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismPlusField_spin n sigma

/--
[sum_oddPrismDobrushinField_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma sum_oddPrismDobrushinField_spin_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  (∑ v, oddPrismDobrushinField n v * spin sigma v) = oddRectangularPrismDobrushinFaceInteraction n sigma := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismDobrushinField_spin n sigma

/--
[oddPrism_plus_inhomogeneousInteraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrism_plus_inhomogeneousInteraction_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  inhomogeneousInteraction (oddPrismInternalEdges n) (fun _ => 1) (oddPrismPlusField n) sigma = -rectangularPrismPlusEnergy 1 sigma := by
-- proof
  apply StatMech.FrontierA.oddPrism_plus_inhomogeneousInteraction n sigma

/--
[oddPrism_dobrushin_inhomogeneousInteraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrism_dobrushin_inhomogeneousInteraction_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  inhomogeneousInteraction (oddPrismInternalEdges n) (fun _ => 1) (oddPrismDobrushinField n) sigma = -oddRectangularPrismDobrushinEnergy 1 n sigma := by
-- proof
  apply StatMech.FrontierA.oddPrism_dobrushin_inhomogeneousInteraction n sigma

/--
[scaledInhomogeneousPartition_oddPrismPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma scaledInhomogeneousPartition_oddPrismPlus_eq
  {beta : Real}
  {n : Nat} :
-- imply
  scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1) (oddPrismPlusField n) beta = rectangularPrismPlusPartition 1 beta (2 * n + 1) (2 * n + 1) n := by
-- proof
  apply StatMech.FrontierA.scaledInhomogeneousPartition_oddPrismPlus beta n

/--
[scaledInhomogeneousPartition_oddPrismDobrushin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma scaledInhomogeneousPartition_oddPrismDobrushin_eq
  {beta : Real}
  {n : Nat} :
-- imply
  scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1) (oddPrismDobrushinField n) beta = rectangularPrismDobrushinPartition 1 beta (2 * n + 1) (2 * n + 1) n := by
-- proof
  apply StatMech.FrontierA.scaledInhomogeneousPartition_oddPrismDobrushin beta n

/--
[boundaryInterfaceFreeEnergy_oddPrism_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma boundaryInterfaceFreeEnergy_oddPrism_eq_eq
  {beta : Real}
  {n : Nat} :
-- imply
  boundaryInterfaceFreeEnergy (oddPrismInternalEdges n) (fun _ => 1) (oddPrismPlusField n) (oddPrismDobrushinField n) beta = StatMech.Ising.rectangularDobrushinFreeEnergy 1 beta (2 * n + 1) (2 * n + 1) n := by
-- proof
  apply StatMech.FrontierA.boundaryInterfaceFreeEnergy_oddPrism_eq beta n

/--
[ginibreChainEdge_oddPrismVerticalChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma ginibreChainEdge_oddPrismVerticalChain_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
  {j : Fin (2 * n)} :
-- imply
  ginibreChainEdge (oddPrismVerticalChain n x y) j = oddPrismInternalEdge n (.inr (.inr (x, y, j))) := by
-- proof
  apply StatMech.FrontierA.ginibreChainEdge_oddPrismVerticalChain n x y j

/--
[ginibreChainEdge_oddPrismVerticalChain_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma ginibreChainEdge_oddPrismVerticalChain_injective_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  Function.Injective (ginibreChainEdge (N := 2 * n) (oddPrismVerticalChain n x y)) := by
-- proof
  apply StatMech.FrontierA.ginibreChainEdge_oddPrismVerticalChain_injective n x y

/--
[ginibreChainEdge_oddPrismVerticalChain_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma ginibreChainEdge_oddPrismVerticalChain_mem_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
  {j : Fin (2 * n)} :
-- imply
  ginibreChainEdge (oddPrismVerticalChain n x y) j ∈ oddPrismInternalEdges n := by
-- proof
  apply StatMech.FrontierA.ginibreChainEdge_oddPrismVerticalChain_mem n x y j

/--
[oddPrismPlus_wJ_eq_fvWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismPlus_wJ_eq_fvWeight_eq
  {beta : Real}
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  wJ (oddPrismInternalEdges n) (fun _ => beta) (fun x => beta * oddPrismPlusField n x) sigma = fvWeight (plusField 3) n (bondFinsetTouch 3 n) beta 0 (rectangularPrismConfigEquivSctBoxDobrushin n sigma) := by
-- proof
  apply StatMech.FrontierA.oddPrismPlus_wJ_eq_fvWeight beta n sigma

/--
[oddPrismPlus_ZJ_eq_fvZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismPlus_ZJ_eq_fvZ_eq
  {beta : Real}
  {n : Nat} :
-- imply
  ZJ (oddPrismInternalEdges n) (fun _ => beta) (fun x => beta * oddPrismPlusField n x) = fvZ (plusField 3) n (bondFinsetTouch 3 n) beta 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismPlus_ZJ_eq_fvZ beta n

/--
[oddPrismPlusSpinMean_eq_plusMeasure_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismPlusSpinMean_eq_plusMeasure_integral_eq
  {beta : Real}
  {n : Nat}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  oddPrismPlusSpinMean beta n v = ∫ omega, spin omega (rectangularPrismSiteEquivSctBoxDobrushin n v).1 ∂(plusMeasure 3 n beta 0 : Measure (ConfigSpace (Site 3))) := by
-- proof
  apply StatMech.FrontierA.oddPrismPlusSpinMean_eq_plusMeasure_integral beta n v

/--
[ginibreChainEdge_oddPrismReverseVerticalChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma ginibreChainEdge_oddPrismReverseVerticalChain_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
  {j : Fin (2 * n)} :
-- imply
  ginibreChainEdge (oddPrismReverseVerticalChain n x y) j = oddPrismInternalEdge n (.inr (.inr (x, y, oddPrismReverseVerticalEdgeIndex n j))) := by
-- proof
  apply StatMech.FrontierA.ginibreChainEdge_oddPrismReverseVerticalChain n x y j

/--
[ginibreChainEdge_oddPrismReverseVerticalChain_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma ginibreChainEdge_oddPrismReverseVerticalChain_injective_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  Function.Injective (ginibreChainEdge (N := 2 * n) (oddPrismReverseVerticalChain n x y)) := by
-- proof
  apply StatMech.FrontierA.ginibreChainEdge_oddPrismReverseVerticalChain_injective n x y

/--
[ginibreChainEdge_oddPrismReverseVerticalChain_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma ginibreChainEdge_oddPrismReverseVerticalChain_mem_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
  {j : Fin (2 * n)} :
-- imply
  ginibreChainEdge (oddPrismReverseVerticalChain n x y) j ∈ oddPrismInternalEdges n := by
-- proof
  apply StatMech.FrontierA.ginibreChainEdge_oddPrismReverseVerticalChain_mem n x y j

/--
[oddPrismReverseVerticalChain_end_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismReverseVerticalChain_end_ne_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) 0 ≠ oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) (2 * n) := by
-- proof
  apply StatMech.FrontierA.oddPrismReverseVerticalChain_end_ne n hn

/--
[oddPrismPlusField_reverse_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismPlusField_reverse_top_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismPlusField n (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) 0) = 1 := by
-- proof
  apply StatMech.FrontierA.oddPrismPlusField_reverse_top n hn

/--
[oddPrismDobrushinField_reverse_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinField_reverse_top_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismDobrushinField n (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) 0) = -1 := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinField_reverse_top n hn

/--
[oddPrismPlusField_reverse_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismPlusField_reverse_bottom_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismPlusField n (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) (2 * n)) = 1 := by
-- proof
  apply StatMech.FrontierA.oddPrismPlusField_reverse_bottom n hn

/--
[oddPrismDobrushinField_reverse_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinField_reverse_bottom_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismDobrushinField n (oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) (2 * n)) = 1 := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinField_reverse_bottom n hn

/--
[oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalAbsCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalAbsCross_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  let v := oddPrismReverseVerticalChain n (oddPrismCenter n) (oddPrismCenter n) (oddPrismPlusSpinMean beta n (v 0) + oddPrismDobrushinSpinMean beta n (v 0)) + (∑ j : Fin (2 * n), |oddPrismPlusSpinMean beta n (v j.val) * oddPrismDobrushinSpinMean beta n (v (j.val + 1)) - oddPrismPlusSpinMean beta n (v (j.val + 1)) * oddPrismDobrushinSpinMean beta n (v j.val)|) + (oddPrismPlusSpinMean beta n (v (2 * n)) - oddPrismDobrushinSpinMean beta n (v (2 * n))) <= deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b (2 * n + 1) (2 * n + 1) n) beta := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalAbsCross beta hbeta n hn

/--
[abs_oddPrismDobrushinSpinMean_le_plusSpinMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma abs_oddPrismDobrushinSpinMean_le_plusSpinMean_eq
  {beta : Real}
  {n : Nat}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n}
-- given
  (hbeta : 0 <= beta) :
-- imply
  |oddPrismDobrushinSpinMean beta n v| <= oddPrismPlusSpinMean beta n v := by
-- proof
  apply StatMech.FrontierA.abs_oddPrismDobrushinSpinMean_le_plusSpinMean beta hbeta n v

/--
[magnetization_le_oddPrismPlusSpinMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma magnetization_le_oddPrismPlusSpinMean_eq
  {beta : Real}
  {n : Nat}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n}
-- given
  (hbeta : 0 <= beta) :
-- imply
  magnetization 3 beta <= oddPrismPlusSpinMean beta n v := by
-- proof
  apply StatMech.FrontierA.magnetization_le_oddPrismPlusSpinMean beta hbeta n v

/--
[oddPrismDobrushinFreeEnergy_deriv_ge_two_mul_magnetization_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinFreeEnergy_deriv_ge_two_mul_magnetization_sq_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  2 * magnetization 3 beta ^ 2 <= deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b (2 * n + 1) (2 * n + 1) n) beta := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinFreeEnergy_deriv_ge_two_mul_magnetization_sq beta hbeta n hn

/--
[ginibreChainEdge_oddPrismReverseVerticalFamily_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma ginibreChainEdge_oddPrismReverseVerticalFamily_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fun q : (Fin (2 * n + 1) × Fin (2 * n + 1)) × Fin (2 * n) => ginibreChainEdge (oddPrismReverseVerticalChain n q.1.1 q.1.2) q.2) := by
-- proof
  apply StatMech.FrontierA.ginibreChainEdge_oddPrismReverseVerticalFamily_injective n

/--
[oddPrismReverseVerticalFamily_end_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismReverseVerticalFamily_end_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fun z : (Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕ (Fin (2 * n + 1) × Fin (2 * n + 1)) => match z with | .inl i => oddPrismReverseVerticalChain n i.1 i.2 0 | .inr i => oddPrismReverseVerticalChain n i.1 i.2 (2 * n)) := by
-- proof
  apply StatMech.FrontierA.oddPrismReverseVerticalFamily_end_injective n hn

/--
[oddPrismPlusField_reverse_top_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismPlusField_reverse_top_ge_one_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  1 <= oddPrismPlusField n (oddPrismReverseVerticalChain n x y 0) := by
-- proof
  apply StatMech.FrontierA.oddPrismPlusField_reverse_top_ge_one n x y

/--
[oddPrismDobrushinField_reverse_top_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinField_reverse_top_eq_neg_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismDobrushinField n (oddPrismReverseVerticalChain n x y 0) = -oddPrismPlusField n (oddPrismReverseVerticalChain n x y 0) := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinField_reverse_top_eq_neg n hn x y

/--
[oddPrismPlusField_reverse_bottom_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismPlusField_reverse_bottom_ge_one_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  1 <= oddPrismPlusField n (oddPrismReverseVerticalChain n x y (2 * n)) := by
-- proof
  apply StatMech.FrontierA.oddPrismPlusField_reverse_bottom_ge_one n x y

/--
[oddPrismDobrushinField_reverse_bottom_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinField_reverse_bottom_eq_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  oddPrismDobrushinField n (oddPrismReverseVerticalChain n x y (2 * n)) = oddPrismPlusField n (oddPrismReverseVerticalChain n x y (2 * n)) := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinField_reverse_bottom_eq n x y

/--
[oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalFamily_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  (∑ i : Fin (2 * n + 1) × Fin (2 * n + 1), let v := oddPrismReverseVerticalChain n i.1 i.2 ((oddPrismPlusSpinMean beta n (v 0) + oddPrismDobrushinSpinMean beta n (v 0)) + (∑ j : Fin (2 * n), |oddPrismPlusSpinMean beta n (v j.val) * oddPrismDobrushinSpinMean beta n (v (j.val + 1)) - oddPrismPlusSpinMean beta n (v (j.val + 1)) * oddPrismDobrushinSpinMean beta n (v j.val)|) + (oddPrismPlusSpinMean beta n (v (2 * n)) - oddPrismDobrushinSpinMean beta n (v (2 * n))))) <= deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b (2 * n + 1) (2 * n + 1) n) beta := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinFreeEnergy_deriv_ge_extendedVerticalFamily beta hbeta n hn

/--
[oddPrismDobrushinFreeEnergy_deriv_ge_area_mul_two_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinFreeEnergy_deriv_ge_area_mul_two_mul_sq_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  (((2 * n + 1 : Nat) : Real) ^ 2) * (2 * magnetization 3 beta ^ 2) <= deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b (2 * n + 1) (2 * n + 1) n) beta := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinFreeEnergy_deriv_ge_area_mul_two_mul_sq beta hbeta n hn

/--
[finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  2 * magnetization 3 beta ^ 2 * (((2 * n + 1 : Nat) : Real) ^ 2) <= fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) beta 0 := by
-- proof
  apply StatMech.FrontierA.finiteInterfaceEnergyDeficit_ge_area_mul_two_mul_sq beta hbeta n hn

/--
[standardCubicInterfaceDensity_deriv_ge_two_mul_sq_via_prism](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_deriv_ge_two_mul_sq_via_prism_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  2 * magnetization 3 beta ^ 2 <= deriv (fun b => standardCubicInterfaceDensity b n) beta := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_deriv_ge_two_mul_sq_via_prism beta hbeta n hn

/--
[oddPrismDobrushinFreeEnergy_deriv_ge_verticalChainCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean)
-/
@[path]
private lemma oddPrismDobrushinFreeEnergy_deriv_ge_verticalChainCross_eq
  {beta : Real}
  {n : Nat}
  {x y : Fin (2 * n + 1)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  (∑ j : Fin (2 * n), (oddPrismPlusSpinMean beta n (oddPrismVerticalChain n x y j.val) * oddPrismDobrushinSpinMean beta n (oddPrismVerticalChain n x y (j.val + 1)) - oddPrismPlusSpinMean beta n (oddPrismVerticalChain n x y (j.val + 1)) * oddPrismDobrushinSpinMean beta n (oddPrismVerticalChain n x y j.val))) <= deriv (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy 1 b (2 * n + 1) (2 * n + 1) n) beta := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinFreeEnergy_deriv_ge_verticalChainCross beta hbeta n x y


-- created on 2026-10-23
