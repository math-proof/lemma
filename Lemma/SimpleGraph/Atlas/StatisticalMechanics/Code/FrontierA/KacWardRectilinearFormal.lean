import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraphLoopExponent_totalDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphLoopExponent_totalDegree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart} :
-- imply
  ons_finsuppTotalDegree (kwGraphLoopExponent G loop) = n := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopExponent_totalDegree G loop

/--
[kwGraphTransition_entry_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphTransition_entry_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {phase : G.Dart → G.Dart → ℂ}
  {dart next : G.Dart} :
-- imply
  kwGraphTransition G weight phase dart next = kwGraphTransition G (fun _ ↦ 1) phase dart next * weight dart.edge := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_entry_factor G weight phase dart next

/--
[kwGraphLoopWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphLoopWeight_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {phase : G.Dart → G.Dart → ℂ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart} :
-- imply
  ons_loopWeight (kwGraphTransition G weight phase) loop = kwGraphLoopScalar G phase loop * (kwGraphLoopExponent G loop).prod (fun edge k ↦ weight edge ^ k) := by
-- proof
  apply StatMech.FrontierA.kwGraphLoopWeight_factor G weight phase loop

/--
[kwGraphFormalLogCoeff_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_eq_tsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {m : Sym2 V →₀ ℕ} :
-- imply
  kwGraphFormalLogCoeff G phase m = -(∑' r : ℕ, (∑ loop : Fin (r + 1) → G.Dart, if kwGraphLoopExponent G loop = m then kwGraphLoopScalar G phase loop else 0) / ((r : ℂ) + 1)) / 2 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_eq_tsum G phase m

/--
[kwGraphFormalLog_constantCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphFormalLog_constantCoeff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ} :
-- imply
  MvPowerSeries.constantCoeff (kwGraphFormalLog G phase) = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLog_constantCoeff G phase

/--
[kwGraphFormalLog_hasSubst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphFormalLog_hasSubst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ} :
-- imply
  PowerSeries.HasSubst (kwGraphFormalLog G phase) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLog_hasSubst G phase

/--
[kwGraphFormalBucket_eval_eq_loopSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphFormalBucket_eval_eq_loopSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {r : ℕ} :
-- imply
  (∑' m : Sym2 V →₀ ℕ, (∑ loop : Fin (r + 1) → G.Dart, if kwGraphLoopExponent G loop = m then kwGraphLoopScalar G phase loop else 0) * ons_mvMonomialValue weight m) = ∑ loop : Fin (r + 1) → G.Dart, ons_loopWeight (kwGraphTransition G weight phase) loop := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalBucket_eval_eq_loopSum G phase weight r

/--
[kwGraphFormalBucket_eval_div_eq_loopSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphFormalBucket_eval_div_eq_loopSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {r : ℕ} :
-- imply
  (∑' m : Sym2 V →₀ ℕ, ((∑ loop : Fin (r + 1) → G.Dart, if kwGraphLoopExponent G loop = m then kwGraphLoopScalar G phase loop else 0) / ((r : ℂ) + 1)) * ons_mvMonomialValue weight m) = (∑ loop : Fin (r + 1) → G.Dart, ons_loopWeight (kwGraphTransition G weight phase) loop) / ((r : ℂ) + 1) := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalBucket_eval_div_eq_loopSum G phase weight r

/--
[norm_kwGraphFormalBucketTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma norm_kwGraphFormalBucketTerm_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {r : ℕ}
  {m : Sym2 V →₀ ℕ} :
-- imply
  ‖kwGraphFormalBucketTerm G phase weight r m‖ ≤ ∑ loop : Fin (r + 1) → G.Dart, if kwGraphLoopExponent G loop = m then ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖ else 0 := by
-- proof
  apply StatMech.FrontierA.norm_kwGraphFormalBucketTerm_le G phase weight r m

/--
[tsum_norm_kwGraphFormalBucketTerm_le_loopSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma tsum_norm_kwGraphFormalBucketTerm_le_loopSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {r : ℕ} :
-- imply
  (∑' m : Sym2 V →₀ ℕ, ‖kwGraphFormalBucketTerm G phase weight r m‖) ≤ ∑ loop : Fin (r + 1) → G.Dart, ‖ons_loopWeight (kwGraphTransition G weight phase) loop‖ := by
-- proof
  apply StatMech.FrontierA.tsum_norm_kwGraphFormalBucketTerm_le_loopSum G phase weight r

/--
[kw_summable_norm_GraphFormalBucketTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_summable_norm_GraphFormalBucketTerm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight phase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  Summable fun r : ℕ ↦ ∑' m : Sym2 V →₀ ℕ, ‖kwGraphFormalBucketTerm G phase weight r m‖ := by
-- proof
  apply StatMech.FrontierA.kw_summable_norm_GraphFormalBucketTerm G phase weight q hq hentry hcard

/--
[kw_summable_norm_GraphFormalBucketTerm_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_summable_norm_GraphFormalBucketTerm_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {r : ℕ} :
-- imply
  Summable fun m : Sym2 V →₀ ℕ ↦ ‖kwGraphFormalBucketTerm G phase weight r m‖ := by
-- proof
  apply StatMech.FrontierA.kw_summable_norm_GraphFormalBucketTerm_fixed G phase weight r

/--
[kw_summable_norm_GraphFormalBucketTerm_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_summable_norm_GraphFormalBucketTerm_product_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight phase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦ ‖kwGraphFormalBucketTerm G phase weight p.1 p.2‖ := by
-- proof
  apply StatMech.FrontierA.kw_summable_norm_GraphFormalBucketTerm_product G phase weight q hq hentry hcard

/--
[kw_summable_GraphFormalBucketTerm_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_summable_GraphFormalBucketTerm_product_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight phase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  Summable fun p : ℕ × (Sym2 V →₀ ℕ) ↦ kwGraphFormalBucketTerm G phase weight p.1 p.2 := by
-- proof
  apply StatMech.FrontierA.kw_summable_GraphFormalBucketTerm_product G phase weight q hq hentry hcard

/--
[kwGraphFormalLog_evalTerm_eq_bucketTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphFormalLog_evalTerm_eq_bucketTsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {m : Sym2 V →₀ ℕ} :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalLog G phase) * ons_mvMonomialValue weight m = ∑' r : ℕ, -kwGraphFormalBucketTerm G phase weight r m / 2 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLog_evalTerm_eq_bucketTsum G phase weight m

/--
[kw_MvSeriesEvalSummable_GraphFormalLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_MvSeriesEvalSummable_GraphFormalLog_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight phase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  ons_MvSeriesEvalSummable (kwGraphFormalLog G phase) weight := by
-- proof
  apply StatMech.FrontierA.kw_MvSeriesEvalSummable_GraphFormalLog G phase weight q hq hentry hcard

/--
[kw_mvSeriesEval_GraphFormalLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_mvSeriesEval_GraphFormalLog_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight phase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  ons_mvSeriesEval (kwGraphFormalLog G phase) weight = -(∑' r : ℕ, (∑ loop : Fin (r + 1) → G.Dart, ons_loopWeight (kwGraphTransition G weight phase) loop) / ((r : ℂ) + 1)) / 2 := by
-- proof
  apply StatMech.FrontierA.kw_mvSeriesEval_GraphFormalLog G phase weight q hq hentry hcard

/--
[kw_mvSeriesEval_GraphFormalRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_mvSeriesEval_GraphFormalRoot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight phase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  ons_mvSeriesEval (kwGraphFormalRoot G phase) weight = ons_detWalkRoot (kwGraphTransition G weight phase) := by
-- proof
  apply StatMech.FrontierA.kw_mvSeriesEval_GraphFormalRoot G phase weight q hq hentry hcard

/--
[kw_MvSeriesEvalSummable_GraphFormalRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_MvSeriesEvalSummable_GraphFormalRoot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight phase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  ons_MvSeriesEvalSummable (kwGraphFormalRoot G phase) weight := by
-- proof
  apply StatMech.FrontierA.kw_MvSeriesEvalSummable_GraphFormalRoot G phase weight q hq hentry hcard

/--
[kw_mvMonomialValue_scaleGraphEdgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_mvMonomialValue_scaleGraphEdgeWeight_eq
  [DecidableEq V]
  {weight : Sym2 V → ℂ}
  {edge : Sym2 V}
  {t : ℂ}
  {m : Sym2 V →₀ ℕ} :
-- imply
  ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge t) m = t ^ m edge * ons_mvMonomialValue weight m := by
-- proof
  apply StatMech.FrontierA.kw_mvMonomialValue_scaleGraphEdgeWeight weight edge t m

/--
[kw_MvSeriesEvalSummable_GraphFormalSecondDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_MvSeriesEvalSummable_GraphFormalSecondDifference_eq
  [DecidableEq V]
  {series : MvPowerSeries (Sym2 V) ℂ}
  {edge : Sym2 V}
  {weight : Sym2 V → ℂ}
-- given
  (h2 : ons_MvSeriesEvalSummable series (kwScaleGraphEdgeWeight weight edge 2))
  (h1 : ons_MvSeriesEvalSummable series weight)
  (h0 : ons_MvSeriesEvalSummable series (kwScaleGraphEdgeWeight weight edge 0)) :
-- imply
  ons_MvSeriesEvalSummable (kwGraphFormalSecondDifference series edge) weight := by
-- proof
  apply StatMech.FrontierA.kw_MvSeriesEvalSummable_GraphFormalSecondDifference series edge weight h2 h1 h0

/--
[kw_mvSeriesEval_GraphFormalSecondDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_mvSeriesEval_GraphFormalSecondDifference_eq
  [DecidableEq V]
  {series : MvPowerSeries (Sym2 V) ℂ}
  {edge : Sym2 V}
  {weight : Sym2 V → ℂ}
-- given
  (h2 : ons_MvSeriesEvalSummable series (kwScaleGraphEdgeWeight weight edge 2))
  (h1 : ons_MvSeriesEvalSummable series weight)
  (h0 : ons_MvSeriesEvalSummable series (kwScaleGraphEdgeWeight weight edge 0)) :
-- imply
  ons_mvSeriesEval (kwGraphFormalSecondDifference series edge) weight = ons_mvSeriesEval series (kwScaleGraphEdgeWeight weight edge 2) - 2 * ons_mvSeriesEval series weight + ons_mvSeriesEval series (kwScaleGraphEdgeWeight weight edge 0) := by
-- proof
  apply StatMech.FrontierA.kw_mvSeriesEval_GraphFormalSecondDifference series edge weight h2 h1 h0

/--
[kwScaleGraphEdgeWeight_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwScaleGraphEdgeWeight_one_eq
  [DecidableEq V]
  {weight : Sym2 V → ℂ}
  {edge : Sym2 V} :
-- imply
  kwScaleGraphEdgeWeight weight edge 1 = weight := by
-- proof
  apply StatMech.FrontierA.kwScaleGraphEdgeWeight_one weight edge

/--
[kwGraphTransition_smulWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kwGraphTransition_smulWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {phase : G.Dart → G.Dart → ℂ}
  {c : ℂ}
  {dart next : G.Dart} :
-- imply
  kwGraphTransition G (fun edge ↦ c * weight edge) phase dart next = c * kwGraphTransition G weight phase dart next := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_smulWeight G weight phase c dart next

/--
[norm_kwGraphTransition_scaleEdge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma norm_kwGraphTransition_scaleEdge_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {phase : G.Dart → G.Dart → ℂ}
  {selected : G.Dart}
  {t : ℂ}
  {r : ℝ}
  {dart next : G.Dart}
-- given
  (hr : 0 ≤ r)
  (ht : ‖t‖ ≤ 2)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight phase dart next‖ ≤ r) :
-- imply
  ‖kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) phase dart next‖ ≤ 2 * r := by
-- proof
  apply StatMech.FrontierA.norm_kwGraphTransition_scaleEdge_le G weight phase selected t r hr ht hentry dart next

/--
[norm_kwScaleColumns_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma norm_kwScaleColumns_le_eq
  [DecidableEq E]
  {S : Finset E}
  {t : ℂ}
  {M : Matrix E E ℂ}
  {r : ℝ}
  {i j : E}
-- given
  (hr : 0 ≤ r)
  (ht : ‖t‖ ≤ 2)
  (hentry : ∀ i j, ‖M i j‖ ≤ r) :
-- imply
  ‖ons_scaleColumns S t M i j‖ ≤ 2 * r := by
-- proof
  apply StatMech.FrontierA.norm_kwScaleColumns_le S t M r hr ht hentry i j

/--
[kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {direction : G.Dart → Fin 4}
  {omega : ℂ}
  {selected : G.Dart}
  {m : Sym2 V →₀ ℕ}
-- given
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (hrepeated : 2 ≤ m selected.edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G (fun dart next ↦ ons_turnW omega (direction next) (direction dart))) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated G direction hdirection omega homega homega_sq selected m hrepeated

/--
[kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean)
-/
@[path]
private lemma kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {direction : G.Dart → Fin 4}
  {omega : ℂ}
  {edge : Sym2 V}
  {m : Sym2 V →₀ ℕ}
-- given
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (hedge : edge ∈ G.edgeFinset)
  (hrepeated : 2 ≤ m edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G (fun dart next ↦ ons_turnW omega (direction next) (direction dart))) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated_edge G direction hdirection omega homega homega_sq edge hedge m hrepeated


-- created on 2026-10-23
