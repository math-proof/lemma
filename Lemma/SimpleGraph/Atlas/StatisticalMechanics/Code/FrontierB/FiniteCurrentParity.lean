import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity.Part2
open MeasureTheory StatMech StatMech.FrontierB


/--
[tanh_nonneg_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma tanh_nonneg_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  0 ≤ Real.tanh x := by
-- proof
  apply StatMech.FrontierB.tanh_nonneg_of_nonneg G hx

/--
[tsum_freeParityRawMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma tsum_freeParityRawMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  ∑' H : Finset (Sym2 V), freeParityRawMass G beta H = ENNReal.ofReal (freeParityPartition G beta) := by
-- proof
  apply StatMech.FrontierB.tsum_freeParityRawMass G beta hbeta

/--
[freeParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma freeParityPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  freeParityPMF G beta hbeta H = freeParityRawMass G beta H * (ENNReal.ofReal (freeParityPartition G beta))⁻¹ := by
-- proof
  apply StatMech.FrontierB.freeParityPMF_apply G beta hbeta H

/--
[freeParityPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma freeParityPartition_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  0 < freeParityPartition G beta := by
-- proof
  apply StatMech.FrontierB.freeParityPartition_pos G beta hbeta

/--
[freeParityMeasure_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma freeParityMeasure_avoid_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (freeParityMeasure G beta hbeta : Measure (Finset (Sym2 V))) {H | Disjoint H F} = ENNReal.ofReal (freeParityAvoidSum G beta F / freeParityPartition G beta) := by
-- proof
  apply StatMech.FrontierB.freeParityMeasure_avoid G beta hbeta F

/--
[boltzmannJ_mul_exp_neg_edgeSpinSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma boltzmannJ_mul_exp_neg_edgeSpinSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {F : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  boltzmannJ G beta (fun _ => 1) s * Real.exp (-beta * edgeSpinSum F s) = boltzmannJ G beta (deletedEdgeCoupling F) s := by
-- proof
  apply StatMech.FrontierB.boltzmannJ_mul_exp_neg_edgeSpinSum G beta F hF s

/--
[deletedEdgeCoupling_cosh_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma deletedEdgeCoupling_cosh_prod_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  (∏ e ∈ G.edgeFinset, Real.cosh (beta * deletedEdgeCoupling F e)) = Real.cosh beta ^ (G.edgeFinset.card - F.card) := by
-- proof
  apply StatMech.FrontierB.deletedEdgeCoupling_cosh_prod G beta F hF

/--
[deletedEdgeCoupling_highTemp_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma deletedEdgeCoupling_highTemp_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {F : Finset (Sym2 V)} :
-- imply
  (∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, highTempSubgraphWeight beta (deletedEdgeCoupling F) H) = freeParityAvoidSum G beta F := by
-- proof
  apply StatMech.FrontierB.deletedEdgeCoupling_highTemp_sum G beta F

/--
[partitionJ_unit_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma partitionJ_unit_highTemp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ} :
-- imply
  partitionJ G beta (fun _ => 1) = (2 : ℝ) ^ Fintype.card V * Real.cosh beta ^ G.edgeFinset.card * freeParityPartition G beta := by
-- proof
  apply StatMech.FrontierB.partitionJ_unit_highTemp G beta

/--
[partitionJ_deleted_highTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma partitionJ_deleted_highTemp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  partitionJ G beta (deletedEdgeCoupling F) = (2 : ℝ) ^ Fintype.card V * Real.cosh beta ^ (G.edgeFinset.card - F.card) * freeParityAvoidSum G beta F := by
-- proof
  apply StatMech.FrontierB.partitionJ_deleted_highTemp G beta F hF

/--
[freeParityAvoidRatio_eq_spinExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma freeParityAvoidRatio_eq_spinExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  freeParityAvoidSum G beta F / freeParityPartition G beta = (∑ s : ConfigSpace V, boltzmannJ G beta (fun _ => 1) s * Real.exp (-beta * edgeSpinSum F s)) / partitionJ G beta (fun _ => 1) * Real.cosh beta ^ F.card := by
-- proof
  apply StatMech.FrontierB.freeParityAvoidRatio_eq_spinExpectation G beta F hF

/--
[freeParityMeasure_avoid_eq_spinExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean)
-/
@[path]
private lemma freeParityMeasure_avoid_eq_spinExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta)
  (hF : F ⊆ G.edgeFinset) :
-- imply
  (freeParityMeasure G beta hbeta : Measure (Finset (Sym2 V))) {H | Disjoint H F} = ENNReal.ofReal (((∑ s : ConfigSpace V, boltzmannJ G beta (fun _ => 1) s * Real.exp (-beta * edgeSpinSum F s)) / partitionJ G beta (fun _ => 1)) * Real.cosh beta ^ F.card) := by
-- proof
  apply StatMech.FrontierB.freeParityMeasure_avoid_eq_spinExpectation G beta hbeta F hF


-- created on 2026-10-23
