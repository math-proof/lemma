import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
open MeasureTheory StatMech StatMech.FrontierB


/--
[boxCurrentSum_pair_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceBoxCurrent.lean)
-/
@[path]
private lemma boxCurrentSum_pair_pos_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y) :
-- imply
  0 < currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} := by
-- proof
  apply StatMech.FrontierB.boxCurrentSum_pair_pos d n beta hbeta x y hxy

/--
[pairSourceBoxCurrentMeasure_prod_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceBoxCurrent.lean)
-/
@[path]
private lemma pairSourceBoxCurrentMeasure_prod_apply_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {C : Set (InfiniteCurrentConfig (Sym2 (Site d)) × InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hC : MeasurableSet C) :
-- imply
  ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _) C = (sourceCurrentPairPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le (fun _ => by positivity) {x, y} {x, y} (boxCurrentSum_pair_pos d n beta hbeta x y hxy) (boxCurrentSum_pair_pos d n beta hbeta x y hxy)).toMeasure ((Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' C) := by
-- proof
  apply StatMech.FrontierB.pairSourceBoxCurrentMeasure_prod_apply d n beta hbeta x y hxy C hC

/--
[boxPairCorrelationConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceBoxCurrent.lean)
-/
@[path]
private lemma boxPairCorrelationConstant_pos_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 < boxPairCorrelationConstant d n beta x y := by
-- proof
  apply StatMech.FrontierB.boxPairCorrelationConstant_pos d n beta hbeta x y

/--
[boxPairCorrelationConstant_le_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceBoxCurrent.lean)
-/
@[path]
private lemma boxPairCorrelationConstant_le_expectation_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y) :
-- imply
  boxPairCorrelationConstant d n beta x y ≤ expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} := by
-- proof
  apply StatMech.FrontierB.boxPairCorrelationConstant_le_expectation d n beta hbeta x y hxy

/--
[pairSourceBoxCurrentMeasure_edge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceBoxCurrent.lean)
-/
@[path]
private lemma pairSourceBoxCurrentMeasure_edge_tail_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {e : (StatMech.FK.boxGraph d n).edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y) :
-- imply
  (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m (boxCurrentEdgeIncl d n e)} = (sourceCurrentMeasure (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le (fun _ => by positivity) {x, y} (boxCurrentSum_pair_pos d n beta hbeta x y hxy) : Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
-- proof
  apply StatMech.FrontierB.pairSourceBoxCurrentMeasure_edge_tail d n beta hbeta x y hxy e K

/--
[pairSourceBoxCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceBoxCurrent.lean)
-/
@[path]
private lemma pairSourceBoxCurrentMeasure_edge_inverse_tail_le_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {e : (StatMech.FK.boxGraph d n).edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hK : 0 < K) :
-- imply
  (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m (boxCurrentEdgeIncl d n e)} ≤ ENNReal.ofReal (Real.exp beta / (boxPairCorrelationConstant d n beta x y * K)) := by
-- proof
  apply StatMech.FrontierB.pairSourceBoxCurrentMeasure_edge_inverse_tail_le d n beta hbeta x y hxy e K hK


-- created on 2026-10-23
