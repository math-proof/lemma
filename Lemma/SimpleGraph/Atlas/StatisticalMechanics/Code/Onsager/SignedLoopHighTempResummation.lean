import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation
open Finset SimpleGraph MeasureTheory Filter Topology StatMech StatMech.Onsager


/--
[ons_setGraphEdgeWeight_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_setGraphEdgeWeight_self_eq
  [Fintype V]
  [DecidableEq V]
  {weight : Sym2 V → Complex}
  {edge : Sym2 V}
  {z : Complex} :
-- imply
  ons_setGraphEdgeWeight weight edge z edge = z := by
-- proof
  apply StatMech.Onsager.ons_setGraphEdgeWeight_self weight edge z

/--
[ons_setGraphEdgeWeight_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_setGraphEdgeWeight_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {weight : Sym2 V → Complex}
  {edge other : Sym2 V}
  {z : Complex}
-- given
  (hne : other ≠ edge) :
-- imply
  ons_setGraphEdgeWeight weight edge z other = weight other := by
-- proof
  apply StatMech.Onsager.ons_setGraphEdgeWeight_of_ne weight edge other z hne

/--
[kwEvenPolynomial_setEdge_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma kwEvenPolynomial_setEdge_affine_eq
  [Fintype V]
  [DecidableEq V]
  {weight : Sym2 V → Complex}
  {edge : Sym2 V}
  {z : Complex} :
-- imply
  kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge z) = kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge 0) + z * ons_kwEvenEdgeCoefficient G weight edge := by
-- proof
  apply StatMech.Onsager.kwEvenPolynomial_setEdge_affine weight edge z

/--
[ons_reciprocalInterpolationCoeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_reciprocalInterpolationCoeff_zero_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex} :
-- imply
  ons_reciprocalInterpolationCoeff q (0 : Fin 3) = q ^ 2 - (q ^ 2)⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_reciprocalInterpolationCoeff_zero q

/--
[ons_reciprocalInterpolationCoeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_reciprocalInterpolationCoeff_one_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex} :
-- imply
  ons_reciprocalInterpolationCoeff q (1 : Fin 3) = ((q ^ 2)⁻¹ + 1) / 2 := by
-- proof
  apply StatMech.Onsager.ons_reciprocalInterpolationCoeff_one q

/--
[ons_reciprocalInterpolationCoeff_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_reciprocalInterpolationCoeff_two_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex} :
-- imply
  ons_reciprocalInterpolationCoeff q (2 : Fin 3) = ((q ^ 2)⁻¹ - 1) / 2 := by
-- proof
  apply StatMech.Onsager.ons_reciprocalInterpolationCoeff_two q

/--
[ons_reciprocalInterpolationValue_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_reciprocalInterpolationValue_zero_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex} :
-- imply
  ons_reciprocalInterpolationValue q (0 : Fin 3) = 0 := by
-- proof
  apply StatMech.Onsager.ons_reciprocalInterpolationValue_zero q

/--
[ons_reciprocalInterpolationValue_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_reciprocalInterpolationValue_one_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex} :
-- imply
  ons_reciprocalInterpolationValue q (1 : Fin 3) = q := by
-- proof
  apply StatMech.Onsager.ons_reciprocalInterpolationValue_one q

/--
[ons_reciprocalInterpolationValue_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_reciprocalInterpolationValue_two_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex} :
-- imply
  ons_reciprocalInterpolationValue q (2 : Fin 3) = -q := by
-- proof
  apply StatMech.Onsager.ons_reciprocalInterpolationValue_two q

/--
[sum_reciprocalInterpolationCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma sum_reciprocalInterpolationCoeff_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex}
-- given
  (hq : q ≠ 0) :
-- imply
  ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s = q ^ 2 := by
-- proof
  apply StatMech.Onsager.sum_reciprocalInterpolationCoeff q hq

/--
[sum_reciprocalInterpolationCoeff_mul_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma sum_reciprocalInterpolationCoeff_mul_value_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex}
-- given
  (hq : q ≠ 0) :
-- imply
  ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s * ons_reciprocalInterpolationValue q s = q := by
-- proof
  apply StatMech.Onsager.sum_reciprocalInterpolationCoeff_mul_value q hq

/--
[sum_reciprocalInterpolationCoeff_mul_value_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma sum_reciprocalInterpolationCoeff_mul_value_sq_eq
  [Fintype V]
  [DecidableEq V]
  {q : Complex}
-- given
  (hq : q ≠ 0) :
-- imply
  ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s * ons_reciprocalInterpolationValue q s ^ 2 = 1 := by
-- proof
  apply StatMech.Onsager.sum_reciprocalInterpolationCoeff_mul_value_sq q hq

/--
[reciprocalInterpolation_affine_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma reciprocalInterpolation_affine_sq_eq
  [Fintype V]
  [DecidableEq V]
  {A B q : Complex}
-- given
  (hq : q ≠ 0) :
-- imply
  q ^ 2 * (A + q⁻¹ * B) ^ 2 = ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s * (A + ons_reciprocalInterpolationValue q s * B) ^ 2 := by
-- proof
  apply StatMech.Onsager.reciprocalInterpolation_affine_sq A B q hq

/--
[reciprocalKWDet_eq_bounded_three_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma reciprocalKWDet_eq_bounded_three_point_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → Complex}
  {edge : Sym2 V}
  {q : Complex}
-- given
  (hq : q ≠ 0) :
-- imply
  q ^ 2 * (1 - kwGraphTransition G (ons_setGraphEdgeWeight weight edge q⁻¹) embedding.turnPhase).det = ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s * (1 - kwGraphTransition G (ons_setGraphEdgeWeight weight edge (ons_reciprocalInterpolationValue q s)) embedding.turnPhase).det := by
-- proof
  apply StatMech.Onsager.reciprocalKWDet_eq_bounded_three_point embedding weight edge q hq

/--
[ons_setGraphEdgeWeightList_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_setGraphEdgeWeightList_apply_eq
  [Fintype V]
  [DecidableEq V]
  {weight : Sym2 V → Complex}
  {z : Complex}
  {edges : List (Sym2 V)}
  {edge : Sym2 V} :
-- imply
  ons_setGraphEdgeWeightList weight z edges edge = if edge ∈ edges then z else weight edge := by
-- proof
  apply StatMech.Onsager.ons_setGraphEdgeWeightList_apply weight z edges edge

/--
[ons_setGraphEdgeWeight_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_setGraphEdgeWeight_comm_eq
  [Fintype V]
  [DecidableEq V]
  {weight : Sym2 V → Complex}
  {e f : Sym2 V}
  {z w : Complex}
-- given
  (hef : e ≠ f) :
-- imply
  ons_setGraphEdgeWeight (ons_setGraphEdgeWeight weight e z) f w = ons_setGraphEdgeWeight (ons_setGraphEdgeWeight weight f w) e z := by
-- proof
  apply StatMech.Onsager.ons_setGraphEdgeWeight_comm weight e f z w hef

/--
[ons_setGraphEdgeWeightList_set_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma ons_setGraphEdgeWeightList_set_comm_eq
  [Fintype V]
  [DecidableEq V]
  {weight : Sym2 V → Complex}
  {edge : Sym2 V}
  {z w : Complex}
  {edges : List (Sym2 V)}
-- given
  (hedge : edge ∉ edges) :
-- imply
  ons_setGraphEdgeWeightList (ons_setGraphEdgeWeight weight edge z) w edges = ons_setGraphEdgeWeight (ons_setGraphEdgeWeightList weight w edges) edge z := by
-- proof
  apply StatMech.Onsager.ons_setGraphEdgeWeightList_set_comm weight edge z w edges hedge

/--
[reciprocalKWDet_list_eq_bounded_resum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma reciprocalKWDet_list_eq_bounded_resum_eq
  [Fintype V]
  [DecidableEq V]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → Complex}
  {q : Complex}
  {edges : List (Sym2 V)}
-- given
  (hq : q ≠ 0)
  (hedges : edges.Nodup) :
-- imply
  q ^ (2 * edges.length) * (1 - kwGraphTransition G (ons_setGraphEdgeWeightList weight q⁻¹ edges) embedding.turnPhase).det = ons_boundedReciprocalKWDetResum G embedding weight q edges := by
-- proof
  apply StatMech.Onsager.reciprocalKWDet_list_eq_bounded_resum embedding weight q hq edges hedges

/--
[norm_reciprocalInterpolationValue_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma norm_reciprocalInterpolationValue_le_eq
  [Fintype V]
  [DecidableEq V]
  {q : Real}
  {s : Fin 3}
-- given
  (hq : 0 ≤ q) :
-- imply
  ‖ons_reciprocalInterpolationValue (q : Complex) s‖ ≤ q := by
-- proof
  apply StatMech.Onsager.norm_reciprocalInterpolationValue_le q hq s

/--
[norm_ons_setGraphEdgeWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma norm_ons_setGraphEdgeWeight_le_eq
  [Fintype V]
  [DecidableEq V]
  {weight : Sym2 V → Complex}
  {edge : Sym2 V}
  {z : Complex}
  {q : Real}
-- given
  (hweight : ∀ f, ‖weight f‖ ≤ q)
  (hz : ‖z‖ ≤ q) :
-- imply
  ∀ f, ‖ons_setGraphEdgeWeight weight edge z f‖ ≤ q := by
-- proof
  apply StatMech.Onsager.norm_ons_setGraphEdgeWeight_le weight edge z q hweight hz

/--
[boundedReciprocalRectKWDetResum_eq_walkResum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma boundedReciprocalRectKWDetResum_eq_walkResum_eq
  [Fintype V]
  [DecidableEq V]
  {M N : Nat}
  {weight : Sym2 (ons_RectDualVertex M N) → Complex}
  {q : Real}
  {edges : List (Sym2 (ons_RectDualVertex M N))}
-- given
  (hq0 : 0 ≤ q)
  (hq : q < ons_signedLoopCriticalWeight)
  (hweight : ∀ edge, ‖weight edge‖ ≤ q) :
-- imply
  ons_boundedReciprocalKWDetResum (ons_rectDualGraph M N) (ons_rectDualStraightLineEmbedding M N) weight (q : Complex) edges = ons_boundedReciprocalRectWalkResum M N weight (q : Complex) edges := by
-- proof
  apply StatMech.Onsager.boundedReciprocalRectKWDetResum_eq_walkResum M N weight q hq0 hq hweight edges

/--
[setGraphEdgeWeightList_uniform_eq_pathDefectWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma setGraphEdgeWeightList_uniform_eq_pathDefectWeight_eq
  [Fintype V]
  [DecidableEq V]
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {q : Real} :
-- imply
  ons_setGraphEdgeWeightList (fun _ ↦ (q : Complex)) (q : Complex)⁻¹ (ons_rectDualPathDefect path).toList = ons_rectDualPathDefectWeight path q := by
-- proof
  apply StatMech.Onsager.setGraphEdgeWeightList_uniform_eq_pathDefectWeight path q

/--
[rectDualPath_sourceDet_eq_bounded_walkResum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma rectDualPath_sourceDet_eq_bounded_walkResum_eq
  [Fintype V]
  [DecidableEq V]
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {q : Real}
-- given
  (hq0 : 0 < q)
  (hq : q < ons_signedLoopCriticalWeight) :
-- imply
  (q : Complex) ^ (2 * (ons_rectDualPathDefect path).card) * ons_rectDualPathCanonicalDefectKWDet path q = ons_boundedReciprocalRectWalkResum M N (fun _ ↦ (q : Complex)) (q : Complex) (ons_rectDualPathDefect path).toList := by
-- proof
  apply StatMech.Onsager.rectDualPath_sourceDet_eq_bounded_walkResum path q hq0 hq

/--
[coe_rectDualPath_finiteTwoPoint_sq_eq_bounded_walkResum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma coe_rectDualPath_finiteTwoPoint_sq_eq_bounded_walkResum_eq
  [Fintype V]
  [DecidableEq V]
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {beta : Real}
-- given
  (hbeta0 : 0 < beta)
  (hbetaC : beta < ons_betaC) :
-- imply
  (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0 (fun spin ↦ StatMech.Ising.spin spin path.source * StatMech.Ising.spin spin path.target) : Complex) ^ 2 = ons_boundedReciprocalRectWalkResum M N (fun _ ↦ (Real.tanh beta : Complex)) (Real.tanh beta : Complex) (ons_rectDualPathDefect path).toList / Complex.exp (-(ons_rectDualWalkExponent M N (fun _ ↦ (Real.tanh beta : Complex)))) := by
-- proof
  apply StatMech.Onsager.coe_rectDualPath_finiteTwoPoint_sq_eq_bounded_walkResum path beta hbeta0 hbetaC

/--
[rectDualPathHighTempWalkRatio_eq_finiteTwoPoint_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma rectDualPathHighTempWalkRatio_eq_finiteTwoPoint_sq_eq
  [Fintype V]
  [DecidableEq V]
  {M N : Nat}
  {path : ons_RectDualPath M N}
  {beta : Real}
-- given
  (hbeta0 : 0 < beta)
  (hbetaC : beta < ons_betaC) :
-- imply
  ons_rectDualPathHighTempWalkRatio path beta = (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0 (fun spin ↦ StatMech.Ising.spin spin path.source * StatMech.Ising.spin spin path.target) : Complex) ^ 2 := by
-- proof
  apply StatMech.Onsager.rectDualPathHighTempWalkRatio_eq_finiteTwoPoint_sq path beta hbeta0 hbetaC

/--
[canonicalHighTempWalkRatio_shifted_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma canonicalHighTempWalkRatio_shifted_tendsto_freeState_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {a b : Site 2}
-- given
  (hbeta0 : 0 < beta)
  (hbetaC : beta < ons_betaC)
  (path : ∀ n, ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)))
  (hsource : ∀ᶠ n in Filter.atTop, ((ons_box2EquivRect (n + 1)).symm (path n).source).1 = a)
  (htarget : ∀ᶠ n in Filter.atTop, ((ons_box2EquivRect (n + 1)).symm (path n).target).1 = b) :
-- imply
  Filter.Tendsto (fun n ↦ ons_rectDualPathHighTempWalkRatio (path n) beta) Filter.atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 beta 0 : MeasureTheory.Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.canonicalHighTempWalkRatio_shifted_tendsto_freeState beta hbeta0 hbetaC path a b hsource htarget

/--
[fixedPairHighTempWalkRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean)
-/
@[path]
private lemma fixedPairHighTempWalkRatio_tendsto_freeState_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {N : Nat}
  {a b : Site 2}
-- given
  (hbeta0 : 0 < beta)
  (hbetaC : beta < ons_betaC)
  (ha : a ∈ StatMech.Lattice.box 2 N)
  (hb : b ∈ StatMech.Lattice.box 2 N)
  (hab : a ≠ b) :
-- imply
  Tendsto (fun n ↦ ons_rectDualPathHighTempWalkRatio (ons_fixedPairRectDualPath N a b ha hb hab n) beta) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.fixedPairHighTempWalkRatio_tendsto_freeState beta hbeta0 hbetaC N a b ha hb hab


-- created on 2026-10-23
