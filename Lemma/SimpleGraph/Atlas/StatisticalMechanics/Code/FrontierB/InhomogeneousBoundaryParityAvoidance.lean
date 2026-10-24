import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.InhomogeneousBoundaryParityAvoidance
open MeasureTheory StatMech StatMech.FrontierB


/--
[boundaryCurrentSum_eq_cosh_mul_inhomogeneousBoundaryParityPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean)
-/
@[path]
private lemma boundaryCurrentSum_eq_cosh_mul_inhomogeneousBoundaryParityPartition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V} :
-- imply
  boundaryCurrentSum G beta J interior = (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * inhomogeneousBoundaryParityPartition G beta J interior := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentSum_eq_cosh_mul_inhomogeneousBoundaryParityPartition G beta J interior

/--
[inhomogeneousBoundaryParityPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousBoundaryParityPartition_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 < inhomogeneousBoundaryParityPartition G beta J interior := by
-- proof
  apply StatMech.FrontierB.inhomogeneousBoundaryParityPartition_pos G beta hbeta J hJ interior

/--
[boundaryNonnegativeParityPMF_apply_eq_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean)
-/
@[path]
private lemma boundaryNonnegativeParityPMF_apply_eq_highTemp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior H = if hvalid : boundaryParityAllowed G interior H then ENNReal.ofReal (highTempSubgraphWeight beta J H) * (ENNReal.ofReal (inhomogeneousBoundaryParityPartition G beta J interior))⁻¹ else 0 := by
-- proof
  apply StatMech.FrontierB.boundaryNonnegativeParityPMF_apply_eq_highTemp G beta hbeta J hJ interior H

/--
[boundaryNonnegativeParityMeasure_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean)
-/
@[path]
private lemma boundaryNonnegativeParityMeasure_avoid_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior).toMeasure {H | Disjoint H F} = ENNReal.ofReal (inhomogeneousBoundaryParityAvoidSum G beta J interior F / inhomogeneousBoundaryParityPartition G beta J interior) := by
-- proof
  apply StatMech.FrontierB.boundaryNonnegativeParityMeasure_avoid G beta hbeta J hJ interior F

/--
[inhomogeneousDeletedCoupling_boundary_highTemp_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousDeletedCoupling_boundary_highTemp_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)} :
-- imply
  (∑ H ∈ G.edgeFinset.powerset, if sources G (edgeIndicatorCurrent H) ∩ interior = ∅ then highTempSubgraphWeight beta (inhomogeneousDeletedCoupling J F) H else 0) = inhomogeneousBoundaryParityAvoidSum G beta J interior F := by
-- proof
  apply StatMech.FrontierB.inhomogeneousDeletedCoupling_boundary_highTemp_sum G beta J interior F

/--
[boundaryPartitionJ_inhomogeneousDeleted_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean)
-/
@[path]
private lemma boundaryPartitionJ_inhomogeneousDeleted_highTemp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  boundaryPartitionJ G beta (inhomogeneousDeletedCoupling J F) interior = (2 : ℝ) ^ interior.card * (∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e)) * inhomogeneousBoundaryParityAvoidSum G beta J interior F := by
-- proof
  apply StatMech.FrontierB.boundaryPartitionJ_inhomogeneousDeleted_highTemp G beta J interior F hF

/--
[inhomogeneousBoundaryParityAvoidRatio_eq_spinExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousBoundaryParityAvoidRatio_eq_spinExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  inhomogeneousBoundaryParityAvoidSum G beta J interior F / inhomogeneousBoundaryParityPartition G beta J interior = ((∑ s : ConfigSpace ↑interior, boltzmannJ G beta J (extendInteriorPlus interior s) * Real.exp (-weightedEdgeSpinSum beta J F (extendInteriorPlus interior s))) / boundaryPartitionJ G beta J interior) * ∏ e ∈ F, Real.cosh (beta * J e) := by
-- proof
  apply StatMech.FrontierB.inhomogeneousBoundaryParityAvoidRatio_eq_spinExpectation G beta J interior F hF

/--
[boundaryCurrentMeasure_parityAvoid_inhomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousBoundaryParityAvoidance.lean)
-/
@[path]
private lemma boundaryCurrentMeasure_parityAvoid_inhomogeneous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (boundaryCurrentPMF G beta J hbeta.le hJ interior).toMeasure {m | Disjoint (currentParitySupport G m) F} = ENNReal.ofReal (inhomogeneousBoundaryParityAvoidSum G beta J interior F / inhomogeneousBoundaryParityPartition G beta J interior) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentMeasure_parityAvoid_inhomogeneous G beta hbeta J hJ interior F


-- created on 2026-10-23
