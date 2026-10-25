import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoxSwitchingBridge.Part3
open MeasureTheory Set SimpleGraph StatMech StatMech.FrontierB


/--
[edgeCurrentOfCurrent_ofEdgeFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma edgeCurrentOfCurrent_ofEdgeFun_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : EdgeCurrent G} :
-- imply
  edgeCurrentOfCurrent G (ofEdgeFun G m) = m := by
-- proof
  apply StatMech.FrontierB.edgeCurrentOfCurrent_ofEdgeFun G m

/--
[finiteBoxCurrentTrace_ofEdgeFun_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma finiteBoxCurrentTrace_ofEdgeFun_add_eq
  {d n : ℕ}
  {m q : EdgeCurrent (StatMech.FK.boxGraph d n)} :
-- imply
  finiteBoxCurrentTrace d n (ofEdgeFun (StatMech.FK.boxGraph d n) (fun e => m e + q e)) = superposedCurrentTrace (extendBoxCurrent d n m, extendBoxCurrent d n q) := by
-- proof
  apply StatMech.FrontierB.finiteBoxCurrentTrace_ofEdgeFun_add d n m q

/--
[currentSubgraph_ofEdgeFun_add_eq_openSubgraphInduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma currentSubgraph_ofEdgeFun_add_eq_openSubgraphInduce_eq
  {d n : ℕ}
  {m q : EdgeCurrent (StatMech.FK.boxGraph d n)} :
-- imply
  currentSubgraph (StatMech.FK.boxGraph d n) (ofEdgeFun (StatMech.FK.boxGraph d n) (fun e => m e + q e)) = openSubgraphInduce d (superposedCurrentTrace (extendBoxCurrent d n m, extendBoxCurrent d n q)) (box d n) := by
-- proof
  apply StatMech.FrontierB.currentSubgraph_ofEdgeFun_add_eq_openSubgraphInduce d n m q

/--
[currentConnected_ofEdgeFun_add_iff_boxConnectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma currentConnected_ofEdgeFun_add_iff_boxConnectionEvent_eq
  {d n : ℕ}
  {m q : EdgeCurrent (StatMech.FK.boxGraph d n)}
  {x y : StatMech.FK.boxVerts d n} :
-- imply
  CurrentConnected (StatMech.FK.boxGraph d n) (ofEdgeFun (StatMech.FK.boxGraph d n) (fun e => m e + q e)) x y ↔ superposedCurrentTrace (extendBoxCurrent d n m, extendBoxCurrent d n q) ∈ boxConnectionEvent n (x : Site d) (y : Site d) := by
-- proof
  apply StatMech.FrontierB.currentConnected_ofEdgeFun_add_iff_boxConnectionEvent d n m q x y

/--
[sourcePairSuperpositionEvent_finiteBoxTracePredicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma sourcePairSuperpositionEvent_finiteBoxTracePredicate_eq
  {d n : ℕ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))} :
-- imply
  sourcePairSuperpositionEvent (StatMech.FK.boxGraph d n) (finiteBoxTracePredicate d n Q) = (Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' (superposedCurrentTrace ⁻¹' Q) := by
-- proof
  apply StatMech.FrontierB.sourcePairSuperpositionEvent_finiteBoxTracePredicate d n Q

/--
[sourcePairSuperpositionEvent_finiteBoxTracePredicate_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma sourcePairSuperpositionEvent_finiteBoxTracePredicate_connected_eq
  {d n : ℕ}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
  {x y : StatMech.FK.boxVerts d n} :
-- imply
  sourcePairSuperpositionEvent (StatMech.FK.boxGraph d n) (fun m => finiteBoxTracePredicate d n Q m ∧ CurrentConnected (StatMech.FK.boxGraph d n) m x y) = (Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' currentPairTraceBoxGate Q n (x : Site d) (y : Site d) := by
-- proof
  apply StatMech.FrontierB.sourcePairSuperpositionEvent_finiteBoxTracePredicate_connected d n Q x y

/--
[freeBoxCurrentMeasure_prod_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_prod_apply_eq
  {d n : ℕ}
  {beta : ℝ}
  {C : Set (InfiniteCurrentConfig (Sym2 (Site d)) × InfiniteCurrentConfig (Sym2 (Site d)))}
-- given
  (hbeta : 0 ≤ beta)
  (hC : MeasurableSet C) :
-- imply
  ((freeBoxCurrentMeasure d n beta hbeta).prod (freeBoxCurrentMeasure d n beta hbeta) : Measure _) C = (sourceCurrentPairPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta (fun _ => by positivity) ∅ ∅ (Ising.acr_currentSum_empty_pos (StatMech.FK.boxGraph d n) beta (fun _ => 1)) (Ising.acr_currentSum_empty_pos (StatMech.FK.boxGraph d n) beta (fun _ => 1))).toMeasure ((Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' C) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_prod_apply d n beta hbeta C hC

/--
[pairSource_free_box_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma pairSource_free_box_switching_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hQ : IsClopen Q) :
-- imply
  ENNReal.ofReal (currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} * currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y}) * ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _) (superposedCurrentTrace ⁻¹' Q) = ENNReal.ofReal (currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) ∅ * currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) ∅) * ((freeBoxCurrentMeasure d n beta hbeta.le).prod (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _) (currentPairTraceBoxGate Q n (x : Site d) (y : Site d)) := by
-- proof
  apply StatMech.FrontierB.pairSource_free_box_switching d n beta hbeta x y hxy Q hQ

/--
[pairSource_free_box_switching_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma pairSource_free_box_switching_normalized_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hQ : IsClopen Q) :
-- imply
  ENNReal.ofReal (expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} ^ 2) * ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _) (superposedCurrentTrace ⁻¹' Q) = ((freeBoxCurrentMeasure d n beta hbeta.le).prod (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _) (currentPairTraceBoxGate Q n (x : Site d) (y : Site d)) := by
-- proof
  apply StatMech.FrontierB.pairSource_free_box_switching_normalized d n beta hbeta x y hxy Q hQ

/--
[pairSource_free_box_switching_normalized_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean)
-/
@[path]
private lemma pairSource_free_box_switching_normalized_real_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {Q : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y)
  (hQ : IsClopen Q) :
-- imply
  expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} ^ 2 * ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _).real (superposedCurrentTrace ⁻¹' Q) = ((freeBoxCurrentMeasure d n beta hbeta.le).prod (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _).real (currentPairTraceBoxGate Q n (x : Site d) (y : Site d)) := by
-- proof
  apply StatMech.FrontierB.pairSource_free_box_switching_normalized_real d n beta hbeta x y hxy Q hQ


-- created on 2026-10-23
