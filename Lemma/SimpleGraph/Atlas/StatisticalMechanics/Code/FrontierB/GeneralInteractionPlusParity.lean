import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.GeneralInteractionPlusParity
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[generalPlusBoxCurrentMeasure_parityAvoid_edgeImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusParity.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_parityAvoid_edgeImage_eq
  {d n : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {E : Finset (Sym2 (interactionBoxVertices d (2 * n + 1)))}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hE : E ⊆ (interactionBoxGraph d (2 * n + 1)).edgeFinset) :
-- imply
  (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder (sym2FinsetMap (Function.Embedding.subtype (fun x : Site d ↦ x ∈ interactionBoxVertices d (2 * n + 1))) E)) = ENNReal.ofReal (inhomogeneousBoundaryParityAvoidSum (interactionBoxGraph d (2 * n + 1)) beta (interactionBoxCoupling J (2 * n + 1)) (interactionPlusInterior d n) E / inhomogeneousBoundaryParityPartition (interactionBoxGraph d (2 * n + 1)) beta (interactionBoxCoupling J (2 * n + 1)) (interactionPlusInterior d n)) := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_parityAvoid_edgeImage J hJ beta hbeta E hE

/--
[generalPlusBoxCurrentMeasure_parityAvoid_nonDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusParity.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_parityAvoid_nonDiagonal_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {n : Nat}
  {F : Finset (Sym2 (Site d))}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 ≤ beta) :
-- imply
  (generalPlusBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder F) = (generalPlusBoxCurrentMeasure J hJ n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityAvoidCylinder (nonDiagonalEdgeFinset F)) := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_parityAvoid_nonDiagonal J hJ beta hbeta n F

/--
[boundaryNonnegativeCurrentLocalParityPMF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusParity.lean)
-/
@[path]
private lemma boundaryNonnegativeCurrentLocalParityPMF_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  PMF.map currentLocalParity (PMF.map (restrictCurrent S) (boundaryCurrentPMF G beta J hbeta.le hJ interior)) = PMF.map (restrictParity G S) (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior) := by
-- proof
  apply StatMech.FrontierB.boundaryNonnegativeCurrentLocalParityPMF G beta hbeta J hJ interior S

/--
[generalPlusBoxCurrentMeasure_pattern_factor_nonDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusParity.lean)
-/
@[path]
private lemma generalPlusBoxCurrentMeasure_pattern_factor_nonDiagonal_eq
  {d n : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
  {a : ↑F → Nat}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 < beta)
  (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d (2 * n + 1))
  (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentCylinder F {a}) = (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) (currentParityPatternCylinder F (currentLocalParity a)) * nonnegativeFiniteParityPMF F (fun e ↦ beta * J e) (fun e : ↑F ↦ mul_nonneg hbeta.le (hJ e.1)) (currentLocalParity a) a := by
-- proof
  apply StatMech.FrontierB.generalPlusBoxCurrentMeasure_pattern_factor_nonDiagonal J hJ beta hbeta F hFbox hFdiag a


-- created on 2026-10-23
