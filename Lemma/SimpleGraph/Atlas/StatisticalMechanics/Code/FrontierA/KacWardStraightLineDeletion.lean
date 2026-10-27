import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineDeletion
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwStraightLineGraph_bothOrientation_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineDeletion.lean)
-/
@[path]
private lemma kwStraightLineGraph_bothOrientation_sum_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {selected : G.Dart} :
-- imply
  (∑ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n) selected selected.symm, StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight embedding.turnPhase) loop) = 0 := by
-- proof
  apply StatMech.FrontierA.kwStraightLineGraph_bothOrientation_sum_zero G embedding weight selected

/--
[kwStraightLineGraph_oneOrientation_sum_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineDeletion.lean)
-/
@[path]
private lemma kwStraightLineGraph_oneOrientation_sum_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {weight : Sym2 V → ℂ}
  {selected : G.Dart} :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → G.Dart ↦ (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm), StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight embedding.turnPhase) loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → G.Dart ↦ (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected), StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight embedding.turnPhase) loop := by
-- proof
  apply StatMech.FrontierA.kwStraightLineGraph_oneOrientation_sum_symm G embedding weight selected

/--
[kwStraightLineGraph_detWalkRoot_delete_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineDeletion.lean)
-/
@[path]
private lemma kwStraightLineGraph_detWalkRoot_delete_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {selected : G.Dart}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  StatMech.Onsager.ons_detWalkRoot (kwGraphTransition G weight embedding.turnPhase) = StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight embedding.turnPhase)) * (1 - ∑' path, StatMech.Onsager.ons_firstReturnWeight (kwGraphTransition G weight embedding.turnPhase) selected selected.symm path) := by
-- proof
  apply StatMech.FrontierA.kwStraightLineGraph_detWalkRoot_delete_pair G embedding weight selected q hq hentry hsmall hcard

/--
[kwStraightLineGraph_detWalkRoot_scaleColumns_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineDeletion.lean)
-/
@[path]
private lemma kwStraightLineGraph_detWalkRoot_scaleColumns_affine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {selected : G.Dart}
  {t : ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight embedding.turnPhase) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight embedding.turnPhase)) = StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight embedding.turnPhase)) * (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight (kwGraphTransition G weight embedding.turnPhase) selected selected.symm path) := by
-- proof
  apply StatMech.FrontierA.kwStraightLineGraph_detWalkRoot_scaleColumns_affine G embedding weight selected t q hq hentry hsmall hcard

/--
[kwStraightLineGraph_detWalkRoot_scaleEdge_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineDeletion.lean)
-/
@[path]
private lemma kwStraightLineGraph_detWalkRoot_scaleEdge_affine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {selected : G.Dart}
  {t : ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖StatMech.Onsager.ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight embedding.turnPhase) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  StatMech.Onsager.ons_detWalkRoot (kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) embedding.turnPhase) = StatMech.Onsager.ons_detWalkRoot (StatMech.Onsager.ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight embedding.turnPhase)) * (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight (kwGraphTransition G weight embedding.turnPhase) selected selected.symm path) := by
-- proof
  apply StatMech.FrontierA.kwStraightLineGraph_detWalkRoot_scaleEdge_affine G embedding weight selected t q hq hentry hsmall hcard


-- created on 2026-10-23
