import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kw_rectilinearGraph_loopRev_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_rectilinearGraph_loopRev_weight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4)
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (loop : Fin n -> G.Dart) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) (StatMech.Onsager.ons_involutiveLoopRev SimpleGraph.Dart.symm loop) = StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) loop := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_loopRev_weight G weight direction hdirection omega homega homega_sq loop

/--
[kw_rectilinearGraph_bothOrientation_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_rectilinearGraph_bothOrientation_sum_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {selected : G.Dart}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4)
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I) :
-- imply
  (∑ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n) selected selected.symm, StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_bothOrientation_sum_zero G weight direction hdirection omega homega homega_sq selected

/--
[kw_rectilinearGraph_oneOrientation_sum_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_rectilinearGraph_oneOrientation_sum_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {selected : G.Dart}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4)
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I) :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n -> G.Dart => (∃ i, loop i = selected) ∧ ¬ ∃ j, loop j = selected.symm), StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n -> G.Dart => (∃ i, loop i = selected.symm) ∧ ¬ ∃ j, loop j = selected), StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) loop := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_oneOrientation_sum_symm G weight direction hdirection omega homega homega_sq selected

/--
[kw_rectilinearGraph_detWalkRoot_delete_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_rectilinearGraph_detWalkRoot_delete_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ℂ}
  {selected : G.Dart}
  {q : ℝ}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4)
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight (fun d e => StatMech.Onsager.ons_turnW omega (direction e) (direction d)) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  StatMech.Onsager.ons_detWalkRoot (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) = StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart)))) * (1 - ∑' path, StatMech.Onsager.ons_firstReturnWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) selected selected.symm path) := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_detWalkRoot_delete_pair G weight direction hdirection omega homega homega_sq selected q hq hentry hsmall hcard

/--
[kw_dart_mem_reversePair_iff_edge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_dart_mem_reversePair_iff_edge_eq_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {selected dart : G.Dart} :
-- imply
  dart ∈ ({selected, selected.symm} : Finset G.Dart) ↔ dart.edge = selected.edge := by
-- proof
  apply StatMech.FrontierA.kw_dart_mem_reversePair_iff_edge_eq selected dart

/--
[kw_scaleColumns_graphTransition_eq_stateWeighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_scaleColumns_graphTransition_eq_stateWeighted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega t : ℂ}
  {selected : G.Dart}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4) :
-- imply
  StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) = StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix direction omega (fun dart => weight dart.edge) (fun dart => if dart.edge = selected.edge then t else 1) (kwGraphNonbacktrackingFactor G) := by
-- proof
  apply StatMech.FrontierA.kw_scaleColumns_graphTransition_eq_stateWeighted G weight direction omega t selected

/--
[kw_rectilinearGraph_detWalkRoot_scaleColumns_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_rectilinearGraph_detWalkRoot_scaleColumns_affine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ℂ}
  {selected : G.Dart}
  {t : ℂ}
  {q : ℝ}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4)
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight (fun d e => StatMech.Onsager.ons_turnW omega (direction e) (direction d))) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart)))) = StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart)))) * (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) selected selected.symm path) := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_detWalkRoot_scaleColumns_affine G weight direction hdirection omega homega homega_sq selected t q hq hentry hsmall hcard

/--
[kwGraphTransition_scaleEdge_entry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kwGraphTransition_scaleEdge_entry_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {selected dart next : G.Dart}
  {t : ℂ}
-- given
  (weight : Sym2 V -> ℂ)
  (phase : G.Dart -> G.Dart -> ℂ) :
-- imply
  kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) phase dart next = (if dart.edge = selected.edge then t else 1) * kwGraphTransition G weight phase dart next := by
-- proof
  apply StatMech.FrontierA.kwGraphTransition_scaleEdge_entry G weight phase selected dart next t

/--
[kw_loopWeight_scaleGraphEdge_eq_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_loopWeight_scaleGraphEdge_eq_scaleColumns_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  [NeZero n]
  {selected : G.Dart}
  {t : ℂ}
-- given
  (weight : Sym2 V -> ℂ)
  (phase : G.Dart -> G.Dart -> ℂ)
  (loop : Fin n -> G.Dart) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) phase) loop = StatMech.Onsager.ons_loopWeight (StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight phase)) loop := by
-- proof
  apply StatMech.FrontierA.kw_loopWeight_scaleGraphEdge_eq_scaleColumns G weight phase selected t loop

/--
[kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {selected : G.Dart}
  {t : ℂ}
-- given
  (weight : Sym2 V -> ℂ)
  (phase : G.Dart -> G.Dart -> ℂ) :
-- imply
  StatMech.Onsager.ons_detWalkRoot (kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) phase) = StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight phase)) := by
-- proof
  apply StatMech.FrontierA.kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns G weight phase selected t

/--
[kw_rectilinearGraph_detWalkRoot_scaleEdge_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean)
-/
@[path]
private lemma kw_rectilinearGraph_detWalkRoot_scaleEdge_affine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ℂ}
  {selected : G.Dart}
  {t : ℂ}
  {q : ℝ}
-- given
  (weight : Sym2 V -> ℂ)
  (direction : G.Dart -> Fin 4)
  (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
  (homega : omega ≠ 0)
  (homega_sq : omega ^ 2 = Complex.I)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight (fun d e => StatMech.Onsager.ons_turnW omega (direction e) (direction d))) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  StatMech.Onsager.ons_detWalkRoot (kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) = StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart)))) * (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight (kwGraphTransition G weight (fun dart next => StatMech.Onsager.ons_turnW omega (direction next) (direction dart))) selected selected.symm path) := by
-- proof
  apply StatMech.FrontierA.kw_rectilinearGraph_detWalkRoot_scaleEdge_affine G weight direction hdirection omega homega homega_sq selected t q hq hentry hsmall hcard


-- created on 2026-10-23
