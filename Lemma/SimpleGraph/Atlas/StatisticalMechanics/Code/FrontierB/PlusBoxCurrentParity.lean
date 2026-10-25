import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[extendInteriorPlus_configEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma extendInteriorPlus_configEquiv_symm_eq
  {d n : ℕ}
  {tau : ConfigSpace (StatMech.FK.boxVerts d n)}
  {v : StatMech.FK.boxVerts d (n + 1)} :
-- imply
  extendInteriorPlus (boxCurrentInterior d (n + 1)) ((boxCurrentInteriorConfigEquiv d n).symm tau) v = if h : v.1 ∈ box d n then tau ⟨v.1, h⟩ else true := by
-- proof
  apply StatMech.FrontierB.extendInteriorPlus_configEquiv_symm d n tau v

/--
[extendInteriorPlus_configEquiv_symm_eq_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma extendInteriorPlus_configEquiv_symm_eq_glue_eq
  {d n : ℕ}
  {tau : ConfigSpace (StatMech.FK.boxVerts d n)}
  {v : StatMech.FK.boxVerts d (n + 1)} :
-- imply
  extendInteriorPlus (boxCurrentInterior d (n + 1)) ((boxCurrentInteriorConfigEquiv d n).symm tau) v = glue (plusField d) tau v.1 := by
-- proof
  apply StatMech.FrontierB.extendInteriorPlus_configEquiv_symm_eq_glue d n tau v

/--
[boxPullbackEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma boxPullbackEdges_subset_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))} :
-- imply
  boxPullbackEdges d n F ⊆ (StatMech.FK.boxGraph d (n + 1)).edgeFinset := by
-- proof
  apply StatMech.FrontierB.boxPullbackEdges_subset d n F

/--
[image_boxPullbackEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma image_boxPullbackEdges_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  (boxPullbackEdges d n F).image (StatMech.FK.edgeIncl d (n + 1)) = F := by
-- proof
  apply StatMech.FrontierB.image_boxPullbackEdges d n F hF

/--
[bond_extendInteriorPlus_eq_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma bond_extendInteriorPlus_eq_glue_eq
  {d n : ℕ}
  {tau : ConfigSpace (StatMech.FK.boxVerts d n)}
  {e : Sym2 (StatMech.FK.boxVerts d (n + 1))} :
-- imply
  bond (extendInteriorPlus (boxCurrentInterior d (n + 1)) ((boxCurrentInteriorConfigEquiv d n).symm tau)) e = bond (glue (plusField d) tau) (StatMech.FK.edgeIncl d (n + 1) e) := by
-- proof
  apply StatMech.FrontierB.bond_extendInteriorPlus_eq_glue d n tau e

/--
[edgeSpinSum_boxPullbackEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma edgeSpinSum_boxPullbackEdges_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))}
  {tau : ConfigSpace (StatMech.FK.boxVerts d n)}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  edgeSpinSum (boxPullbackEdges d n F) (extendInteriorPlus (boxCurrentInterior d (n + 1)) ((boxCurrentInteriorConfigEquiv d n).symm tau)) = edgeSpinSum F (glue (plusField d) tau) := by
-- proof
  apply StatMech.FrontierB.edgeSpinSum_boxPullbackEdges d n F hF tau

/--
[boltzmannJ_extendInteriorPlus_eq_fvWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma boltzmannJ_extendInteriorPlus_eq_fvWeight_eq
  {d n : ℕ}
  {beta : ℝ}
  {tau : ConfigSpace (StatMech.FK.boxVerts d n)} :
-- imply
  boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (extendInteriorPlus (boxCurrentInterior d (n + 1)) ((boxCurrentInteriorConfigEquiv d n).symm tau)) = Real.exp (beta * ((Finset.image (StatMech.FK.edgeIncl d (n + 1)) (StatMech.FK.boxGraph d (n + 1)).edgeFinset) \ bondFinsetTouch d n).card) * fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau := by
-- proof
  apply StatMech.FrontierB.boltzmannJ_extendInteriorPlus_eq_fvWeight d n beta tau

/--
[boundaryPartitionJ_box_eq_fvZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma boundaryPartitionJ_box_eq_fvZ_eq
  {d n : ℕ}
  {beta : ℝ} :
-- imply
  boundaryPartitionJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1)) = Real.exp (beta * ((Finset.image (StatMech.FK.edgeIncl d (n + 1)) (StatMech.FK.boxGraph d (n + 1)).edgeFinset) \ bondFinsetTouch d n).card) * fvZ (plusField d) n (bondFinsetTouch d n) beta 0 := by
-- proof
  apply StatMech.FrontierB.boundaryPartitionJ_box_eq_fvZ d n beta

/--
[boundarySpinExpectation_box_eq_plusIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma boundarySpinExpectation_box_eq_plusIntegral_eq
  {d n : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  ((∑ s : ConfigSpace ↑(boxCurrentInterior d (n + 1)), boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (extendInteriorPlus (boxCurrentInterior d (n + 1)) s) * Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F) (extendInteriorPlus (boxCurrentInterior d (n + 1)) s))) / boundaryPartitionJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1))) = ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.boundarySpinExpectation_box_eq_plusIntegral d n beta F hF

/--
[preimage_currentParityAvoidCylinder_extendBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma preimage_currentParityAvoidCylinder_extendBoxCurrent_eq
  {d n : ℕ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  extendBoxCurrent d (n + 1) ⁻¹' currentParityAvoidCylinder F = {m | Disjoint (currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m) (boxPullbackEdges d n F)} := by
-- proof
  apply StatMech.FrontierB.preimage_currentParityAvoidCylinder_extendBoxCurrent d n F hF

/--
[plusBoxCurrentMeasure_parityAvoid_eq_plusIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_parityAvoid_eq_plusIntegral_eq
  {d n : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 ≤ beta)
  (hF : F ⊆ bondFinsetTouch d n) :
-- imply
  (plusBoxCurrentMeasure d (n + 1) beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder F) = ENNReal.ofReal ((∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) * Real.cosh beta ^ F.card) := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_parityAvoid_eq_plusIntegral d n beta hbeta F hF


-- created on 2026-10-23
