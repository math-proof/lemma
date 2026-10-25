import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEval.Part2
open StatMech StatMech.Onsager


/--
[ons_tsum_finite_exponent_buckets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_tsum_finite_exponent_buckets_eq
  [Fintype I]
  [DecidableEq E]
  {exponent : I → E}
  {scalar : I → ℂ}
  {value : E → ℂ} :
-- imply
  (∑' m : E, (∑ i : I, if exponent i = m then scalar i else 0) * value m) = ∑ i : I, scalar i * value (exponent i) := by
-- proof
  apply StatMech.Onsager.ons_tsum_finite_exponent_buckets exponent scalar value

/--
[ons_decFormalBucket_eval_eq_loopSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_decFormalBucket_eval_eq_loopSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega u v : ℂ}
  {decWeight : ons_DecEdge L → ℂ}
  {r : ℕ} :
-- imply
  (∑' m : ons_DecEdge L →₀ ℕ, (∑ d : Fin (r + 1) → ons_Dart L, if ons_decLoopExponent L d = m then ons_decLoopScalar L omega u v d else 0) * m.prod (fun edge n ↦ decWeight edge ^ n)) = ∑ d : Fin (r + 1) → ons_Dart L, ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d := by
-- proof
  apply StatMech.Onsager.ons_decFormalBucket_eval_eq_loopSum L omega u v decWeight r

/--
[ons_decFormalBucket_eval_div_eq_loopSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_decFormalBucket_eval_div_eq_loopSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega u v : ℂ}
  {decWeight : ons_DecEdge L → ℂ}
  {r : ℕ} :
-- imply
  (∑' m : ons_DecEdge L →₀ ℕ, ((∑ d : Fin (r + 1) → ons_Dart L, if ons_decLoopExponent L d = m then ons_decLoopScalar L omega u v d else 0) / ((r : ℂ) + 1)) * m.prod (fun edge n ↦ decWeight edge ^ n)) = (∑ d : Fin (r + 1) → ons_Dart L, ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d) / ((r : ℂ) + 1) := by
-- proof
  apply StatMech.Onsager.ons_decFormalBucket_eval_div_eq_loopSum L omega u v decWeight r

/--
[ons_tsum_finite_exponent_buckets_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_tsum_finite_exponent_buckets_real_eq
  [Fintype I]
  [DecidableEq E]
  {exponent : I → E}
  {scalar : I → ℝ} :
-- imply
  (∑' m : E, ∑ i : I, if exponent i = m then scalar i else 0) = ∑ i : I, scalar i := by
-- proof
  apply StatMech.Onsager.ons_tsum_finite_exponent_buckets_real exponent scalar

/--
[norm_ons_decFormalBucketTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma norm_ons_decFormalBucketTerm_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega u v : ℂ}
  {decWeight : ons_DecEdge L → ℂ}
  {r : ℕ}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  ‖ons_decFormalBucketTerm L omega u v decWeight r m‖ ≤ ∑ d : Fin (r + 1) → ons_Dart L, if ons_decLoopExponent L d = m then ‖ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d‖ else 0 := by
-- proof
  apply StatMech.Onsager.norm_ons_decFormalBucketTerm_le L omega u v decWeight r m

/--
[tsum_norm_ons_decFormalBucketTerm_le_loopSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma tsum_norm_ons_decFormalBucketTerm_le_loopSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega u v : ℂ}
  {decWeight : ons_DecEdge L → ℂ}
  {r : ℕ} :
-- imply
  (∑' m : ons_DecEdge L →₀ ℕ, ‖ons_decFormalBucketTerm L omega u v decWeight r m‖) ≤ ∑ d : Fin (r + 1) → ons_Dart L, ‖ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d‖ := by
-- proof
  apply StatMech.Onsager.tsum_norm_ons_decFormalBucketTerm_le_loopSum L omega u v decWeight r

/--
[ons_summable_norm_decFormalBucketTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_summable_norm_decFormalBucketTerm_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  Summable fun r : ℕ ↦ ∑' m : ons_DecEdge L →₀ ℕ, ‖ons_decFormalBucketTerm L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) decWeight r m‖ := by
-- proof
  apply StatMech.Onsager.ons_summable_norm_decFormalBucketTerm L decWeight a b q hq hall hext hcard

/--
[ons_summable_norm_decFormalBucketTerm_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_summable_norm_decFormalBucketTerm_fixed_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega u v : ℂ}
  {decWeight : ons_DecEdge L → ℂ}
  {r : ℕ} :
-- imply
  Summable fun m : ons_DecEdge L →₀ ℕ ↦ ‖ons_decFormalBucketTerm L omega u v decWeight r m‖ := by
-- proof
  apply StatMech.Onsager.ons_summable_norm_decFormalBucketTerm_fixed L omega u v decWeight r

/--
[ons_summable_norm_decFormalBucketTerm_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_summable_norm_decFormalBucketTerm_product_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  Summable fun p : ℕ × (ons_DecEdge L →₀ ℕ) ↦ ‖ons_decFormalBucketTerm L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) decWeight p.1 p.2‖ := by
-- proof
  apply StatMech.Onsager.ons_summable_norm_decFormalBucketTerm_product L decWeight a b q hq hall hext hcard

/--
[ons_summable_decFormalBucketTerm_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_summable_decFormalBucketTerm_product_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  Summable fun p : ℕ × (ons_DecEdge L →₀ ℕ) ↦ ons_decFormalBucketTerm L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) decWeight p.1 p.2 := by
-- proof
  apply StatMech.Onsager.ons_summable_decFormalBucketTerm_product L decWeight a b q hq hall hext hcard

/--
[ons_decFormalLog_evalTerm_eq_bucketTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_decFormalLog_evalTerm_eq_bucketTsum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  MvPowerSeries.coeff m (ons_decFormalLog L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) * ons_mvMonomialValue decWeight m = ∑' r : ℕ, -ons_decFormalBucketTerm L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) decWeight r m / 2 := by
-- proof
  apply StatMech.Onsager.ons_decFormalLog_evalTerm_eq_bucketTsum L decWeight a b m

/--
[ons_MvSeriesEvalSummable_decFormalLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_MvSeriesEvalSummable_decFormalLog_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_MvSeriesEvalSummable (ons_decFormalLog L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) decWeight := by
-- proof
  apply StatMech.Onsager.ons_MvSeriesEvalSummable_decFormalLog L decWeight a b q hq hall hext hcard

/--
[ons_mvSeriesEval_decFormalLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_mvSeriesEval_decFormalLog_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_mvSeriesEval (ons_decFormalLog L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) decWeight = -(∑' r : ℕ, (∑ d : Fin (r + 1) → ons_Dart L, ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) d) / ((r : ℂ) + 1)) / 2 := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_decFormalLog L decWeight a b q hq hall hext hcard

/--
[ons_mvSeriesEval_decFormalRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_mvSeriesEval_decFormalRoot_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_mvSeriesEval (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) decWeight = ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_decFormalRoot L decWeight a b q hq hall hext hcard

/--
[ons_MvSeriesEvalSummable_decFormalRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_MvSeriesEvalSummable_decFormalRoot_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_MvSeriesEvalSummable (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) decWeight := by
-- proof
  apply StatMech.Onsager.ons_MvSeriesEvalSummable_decFormalRoot L decWeight a b q hq hall hext hcard

/--
[ons_detWalkRoot_eq_decoratedFullWeightedSpinSum_of_formal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEval.lean)
-/
@[path]
private lemma ons_detWalkRoot_eq_decoratedFullWeightedSpinSum_of_formal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hformal : ons_decoratedFormalKacWardIdentity L)
  (hq : 0 ≤ q)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1)
  (hext : ∀ d, ‖decWeight s(d, ons_dartRev L d)‖ ≤ q)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_decoratedFullWeightedSpinSum L decWeight a b := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_eq_decoratedFullWeightedSpinSum_of_formal L hformal decWeight a b q hq hall hext hcard


-- created on 2026-10-23
