import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FinitePlusBoundarySwitchingBridge
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[plusPairSource_pairSource_prod_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FinitePlusBoundarySwitchingBridge.lean)
-/
@[path]
private lemma plusPairSource_pairSource_prod_apply_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {C : Set (InfiniteCurrentConfig (Sym2 (Site d)) × InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hC : MeasurableSet C) :
-- imply
  ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)) : Measure _) C = (boundarySourceCurrentPairPMF (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) hbeta.le (fun _ => by positivity) (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y} {boxSiteSucc x, boxSiteSucc y} (plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy) (boxCurrentSum_pair_pos d (n + 1) beta hbeta (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy))).toMeasure ((Prod.map (extendBoxCurrent d (n + 1)) (extendBoxCurrent d (n + 1))) ⁻¹' C) := by
-- proof
  apply StatMech.FrontierB.plusPairSource_pairSource_prod_apply d n beta hbeta x y hxy C hC

/--
[plus_free_BoxCurrentMeasure_prod_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FinitePlusBoundarySwitchingBridge.lean)
-/
@[path]
private lemma plus_free_BoxCurrentMeasure_prod_apply_eq
  {d n : ℕ}
  {beta : ℝ}
  {C : Set (InfiniteCurrentConfig (Sym2 (Site d)) × InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 ≤ beta)
  (hC : MeasurableSet C) :
-- imply
  ((plusBoxCurrentMeasure d n beta hbeta).prod (freeBoxCurrentMeasure d n beta hbeta) : Measure _) C = (boundarySourceCurrentPairPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta (fun _ => by positivity) (boxCurrentInterior d n) ∅ ∅ (lt_of_lt_of_le Real.zero_lt_one (one_le_boundaryCurrentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta (fun _ => by positivity) (boxCurrentInterior d n))) (Ising.acr_currentSum_empty_pos (StatMech.FK.boxGraph d n) beta (fun _ => 1))).toMeasure ((Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' C) := by
-- proof
  apply StatMech.FrontierB.plus_free_BoxCurrentMeasure_prod_apply d n beta hbeta C hC

/--
[plusPair_pairSource_plus_free_box_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FinitePlusBoundarySwitchingBridge.lean)
-/
@[path]
private lemma plusPair_pairSource_plus_free_box_switching_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hQ : IsClopen Q) :
-- imply
  ENNReal.ofReal (boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y} * currentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) {boxSiteSucc x, boxSiteSucc y}) * ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)) : Measure _) (superposedCurrentTrace ⁻¹' Q) = ENNReal.ofReal (boundaryCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1)) * currentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) ∅) * ((plusBoxCurrentMeasure d (n + 1) beta hbeta.le).prod (freeBoxCurrentMeasure d (n + 1) beta hbeta.le) : Measure _) (currentPairTraceBoxGate Q (n + 1) x.1 y.1) := by
-- proof
  apply StatMech.FrontierB.plusPair_pairSource_plus_free_box_switching d n beta hbeta x y hxy Q hQ

/--
[plusPair_pairSource_plus_free_box_switching_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FinitePlusBoundarySwitchingBridge.lean)
-/
@[path]
private lemma plusPair_pairSource_plus_free_box_switching_normalized_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hQ : IsClopen Q) :
-- imply
  ENNReal.ofReal ((∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) * expectationJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) {boxSiteSucc x, boxSiteSucc y}) * ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)) : Measure _) (superposedCurrentTrace ⁻¹' Q) = ((plusBoxCurrentMeasure d (n + 1) beta hbeta.le).prod (freeBoxCurrentMeasure d (n + 1) beta hbeta.le) : Measure _) (currentPairTraceBoxGate Q (n + 1) x.1 y.1) := by
-- proof
  apply StatMech.FrontierB.plusPair_pairSource_plus_free_box_switching_normalized d n beta hbeta x y hxy Q hQ

/--
[plusPair_pairSource_plus_free_box_switching_normalized_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FinitePlusBoundarySwitchingBridge.lean)
-/
@[path]
private lemma plusPair_pairSource_plus_free_box_switching_normalized_real_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hQ : IsClopen Q) :
-- imply
  ((∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) * expectationJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) {boxSiteSucc x, boxSiteSucc y}) * ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)) : Measure _).real (superposedCurrentTrace ⁻¹' Q) = ((plusBoxCurrentMeasure d (n + 1) beta hbeta.le).prod (freeBoxCurrentMeasure d (n + 1) beta hbeta.le) : Measure _).real (currentPairTraceBoxGate Q (n + 1) x.1 y.1) := by
-- proof
  apply StatMech.FrontierB.plusPair_pairSource_plus_free_box_switching_normalized_real d n beta hbeta x y hxy Q hQ


-- created on 2026-10-23
