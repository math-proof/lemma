import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
open MeasureTheory StatMech StatMech.FrontierB


/--
[inhomogeneousParityFiberMass_eq_cosh_mul_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousParityFiberMass_eq_cosh_mul_highTemp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hH : H ⊆ G.edgeFinset) :
-- imply
  inhomogeneousParityFiberMass G (fun e => beta * J e) H = (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * highTempSubgraphWeight beta J H := by
-- proof
  apply StatMech.FrontierB.inhomogeneousParityFiberMass_eq_cosh_mul_highTemp G beta J H hH

/--
[partitionJ_eq_cosh_mul_inhomogeneousParityPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma partitionJ_eq_cosh_mul_inhomogeneousParityPartition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  partitionJ G beta J = (2 : ℝ) ^ Fintype.card V * (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * inhomogeneousParityPartition G beta J := by
-- proof
  apply StatMech.FrontierB.partitionJ_eq_cosh_mul_inhomogeneousParityPartition G beta J

/--
[currentSum_eq_cosh_mul_inhomogeneousParityPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma currentSum_eq_cosh_mul_inhomogeneousParityPartition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  currentSum G beta J ∅ = (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * inhomogeneousParityPartition G beta J := by
-- proof
  apply StatMech.FrontierB.currentSum_eq_cosh_mul_inhomogeneousParityPartition G beta J

/--
[inhomogeneousParityPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousParityPartition_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 < inhomogeneousParityPartition G beta J := by
-- proof
  apply StatMech.FrontierB.inhomogeneousParityPartition_pos G beta hbeta J hJ

/--
[sourcelessNonnegativeParityPMF_apply_eq_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma sourcelessNonnegativeParityPMF_apply_eq_highTemp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  sourcelessNonnegativeParityPMF G beta J hbeta.le hJ H = if hvalid : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then ENNReal.ofReal (highTempSubgraphWeight beta J H) * (ENNReal.ofReal (inhomogeneousParityPartition G beta J))⁻¹ else 0 := by
-- proof
  apply StatMech.FrontierB.sourcelessNonnegativeParityPMF_apply_eq_highTemp G beta hbeta J hJ H

/--
[sourcelessNonnegativeParityMeasure_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma sourcelessNonnegativeParityMeasure_avoid_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).toMeasure {H | Disjoint H F} = ENNReal.ofReal (inhomogeneousParityAvoidSum G beta J F / inhomogeneousParityPartition G beta J) := by
-- proof
  apply StatMech.FrontierB.sourcelessNonnegativeParityMeasure_avoid G beta hbeta J hJ F

/--
[boltzmannJ_mul_exp_neg_weightedEdgeSpinSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma boltzmannJ_mul_exp_neg_weightedEdgeSpinSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  boltzmannJ G beta J s * Real.exp (-weightedEdgeSpinSum beta J F s) = boltzmannJ G beta (inhomogeneousDeletedCoupling J F) s := by
-- proof
  apply StatMech.FrontierB.boltzmannJ_mul_exp_neg_weightedEdgeSpinSum G beta J F hF s

/--
[inhomogeneousDeletedCoupling_cosh_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousDeletedCoupling_cosh_prod_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  (∏ e ∈ G.edgeFinset, Real.cosh (beta * inhomogeneousDeletedCoupling J F e)) = ∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e) := by
-- proof
  apply StatMech.FrontierB.inhomogeneousDeletedCoupling_cosh_prod G beta J F hF

/--
[inhomogeneousDeletedCoupling_highTemp_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousDeletedCoupling_highTemp_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)} :
-- imply
  (∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, highTempSubgraphWeight beta (inhomogeneousDeletedCoupling J F) H) = inhomogeneousParityAvoidSum G beta J F := by
-- proof
  apply StatMech.FrontierB.inhomogeneousDeletedCoupling_highTemp_sum G beta J F

/--
[partitionJ_inhomogeneousDeleted_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma partitionJ_inhomogeneousDeleted_highTemp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  partitionJ G beta (inhomogeneousDeletedCoupling J F) = (2 : ℝ) ^ Fintype.card V * (∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e)) * inhomogeneousParityAvoidSum G beta J F := by
-- proof
  apply StatMech.FrontierB.partitionJ_inhomogeneousDeleted_highTemp G beta J F hF

/--
[inhomogeneousParityAvoidRatio_eq_spinExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousParityAvoidRatio_eq_spinExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  inhomogeneousParityAvoidSum G beta J F / inhomogeneousParityPartition G beta J = ((∑ s : ConfigSpace V, boltzmannJ G beta J s * Real.exp (-weightedEdgeSpinSum beta J F s)) / partitionJ G beta J) * ∏ e ∈ F, Real.cosh (beta * J e) := by
-- proof
  apply StatMech.FrontierB.inhomogeneousParityAvoidRatio_eq_spinExpectation G beta J F hF

/--
[inhomogeneousParityAvoidRatio_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma inhomogeneousParityAvoidRatio_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  inhomogeneousParityAvoidSum G beta J F / inhomogeneousParityPartition G beta J = expJ G.edgeFinset (fun e => beta * J e) (fun _ => 0) (fun s => Real.exp (-weightedEdgeSpinSum beta J F s)) * ∏ e ∈ F, Real.cosh (beta * J e) := by
-- proof
  apply StatMech.FrontierB.inhomogeneousParityAvoidRatio_eq_expJ G beta J F hF

/--
[sourcelessCurrentMeasure_parityAvoid_inhomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_parityAvoid_inhomogeneous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (sourcelessCurrentPMF G beta J hbeta.le hJ).toMeasure {m | Disjoint (currentParitySupport G m) F} = ENNReal.ofReal (inhomogeneousParityAvoidSum G beta J F / inhomogeneousParityPartition G beta J) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_parityAvoid_inhomogeneous G beta hbeta J hJ F

/--
[exp_neg_weightedEdgeSpinSum_eq_spinProd_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma exp_neg_weightedEdgeSpinSum_eq_spinProd_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {F : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (hF : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  Real.exp (-weightedEdgeSpinSum beta J F s) = ∑ T ∈ F.powerset, weightedEdgeExpansionCoeff beta J F T * spinProd (edgeBoundary (F \ T)) s := by
-- proof
  apply StatMech.FrontierB.exp_neg_weightedEdgeSpinSum_eq_spinProd_sum G beta J F hF s

/--
[expJ_exp_neg_weightedEdgeSpinSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean)
-/
@[path]
private lemma expJ_exp_neg_weightedEdgeSpinSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {E : Finset (Sym2 V)}
  {beta : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (K hfJ : Sym2 V → ℝ)
  (hf : V → ℝ)
  (hF : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  expJ E K hf (fun s => Real.exp (-weightedEdgeSpinSum beta hfJ F s)) = ∑ T ∈ F.powerset, weightedEdgeExpansionCoeff beta hfJ F T * expJ E K hf (spinProd (edgeBoundary (F \ T))) := by
-- proof
  apply StatMech.FrontierB.expJ_exp_neg_weightedEdgeSpinSum G E K hfJ hf beta F hF


-- created on 2026-10-23
