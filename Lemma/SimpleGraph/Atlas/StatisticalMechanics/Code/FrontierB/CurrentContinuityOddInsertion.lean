import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityOddInsertion.Part2
open StatMech StatMech.FrontierB


/--
[encodeCurrentEdgeOdd_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean)
-/
@[path]
private lemma encodeCurrentEdgeOdd_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset} :
-- imply
  Function.Injective (encodeCurrentEdgeOdd G e) := by
-- proof
  apply StatMech.FrontierB.encodeCurrentEdgeOdd_injective G e

/--
[encodeCurrentEdgeOdd_eq_add_unitFlux_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean)
-/
@[path]
private lemma encodeCurrentEdgeOdd_eq_add_unitFlux_of_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm : m e = 0) :
-- imply
  encodeCurrentEdgeOdd G e m = fun f => m f + currentUnitFlux G e f := by
-- proof
  apply StatMech.FrontierB.encodeCurrentEdgeOdd_eq_add_unitFlux_of_zero G e m hm

/--
[sources_currentUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean)
-/
@[path]
private lemma sources_currentUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset} :
-- imply
  sources G (ofEdgeFun G (currentUnitFlux G e)) = {e.1.out.1, e.1.out.2} := by
-- proof
  apply StatMech.FrontierB.sources_currentUnitFlux G e

/--
[sources_encodeCurrentEdgeOdd_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean)
-/
@[path]
private lemma sources_encodeCurrentEdgeOdd_of_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm : m e = 0) :
-- imply
  sources G (ofEdgeFun G (encodeCurrentEdgeOdd G e m)) = sources G (ofEdgeFun G m) ∆ {e.1.out.1, e.1.out.2} := by
-- proof
  apply StatMech.FrontierB.sources_encodeCurrentEdgeOdd_of_zero G e m hm

/--
[weight_encodeCurrentEdgeOdd_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean)
-/
@[path]
private lemma weight_encodeCurrentEdgeOdd_of_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm : m e = 0) :
-- imply
  weight G beta (fun _ => 1) (ofEdgeFun G (encodeCurrentEdgeOdd G e m)) = beta * weight G beta (fun _ => 1) (ofEdgeFun G m) := by
-- proof
  apply StatMech.FrontierB.weight_encodeCurrentEdgeOdd_of_zero G beta e m hm

/--
[currentConnected_edgeEndpoints_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean)
-/
@[path]
private lemma currentConnected_edgeEndpoints_of_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeFinset}
  {m : EdgeCurrent G}
-- given
  (hm : 0 < m e) :
-- imply
  CurrentConnected G (ofEdgeFun G m) e.1.out.1 e.1.out.2 := by
-- proof
  apply StatMech.FrontierB.currentConnected_edgeEndpoints_of_pos G e m hm

/--
[beta_mul_boundarySource_notConnected_le_exteriorConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean)
-/
@[path]
private lemma beta_mul_boundarySource_notConnected_le_exteriorConnection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {interior : Finset V}
  {e : G.edgeFinset}
-- given
  (hbeta : 0 < beta)
  (hleft : e.1.out.1 ∈ interior)
  (hright : e.1.out.2 ∈ interior) :
-- imply
  beta * boundarySourceGatedPairSum G beta (fun _ => 1) interior {e.1.out.1, e.1.out.2} ∅ (fun m => ¬ CurrentConnected G m e.1.out.1 e.1.out.2) ≤ boundarySourceGatedPairSum G beta (fun _ => 1) interior ∅ ∅ (fun m => ∃ z : V, z ∉ interior ∧ CurrentConnected G m e.1.out.1 z) := by
-- proof
  apply StatMech.FrontierB.beta_mul_boundarySource_notConnected_le_exteriorConnection G beta hbeta interior e hleft hright

/--
[beta_mul_boundarySource_twoPoint_gap_le_exteriorConnection_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean)
-/
@[path]
private lemma beta_mul_boundarySource_twoPoint_gap_le_exteriorConnection_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {interior : Finset V}
  {e : G.edgeFinset}
-- given
  (hbeta : 0 < beta)
  (hleft : e.1.out.1 ∈ interior)
  (hright : e.1.out.2 ∈ interior) :
-- imply
  beta * (boundarySourceCurrentSum G beta (fun _ => 1) interior {e.1.out.1, e.1.out.2} / boundarySourceCurrentSum G beta (fun _ => 1) interior ∅ - currentSum G beta (fun _ => 1) {e.1.out.1, e.1.out.2} / currentSum G beta (fun _ => 1) ∅) ≤ boundarySourceGatedPairSum G beta (fun _ => 1) interior ∅ ∅ (fun m => ∃ z : V, z ∉ interior ∧ CurrentConnected G m e.1.out.1 z) / (boundarySourceCurrentSum G beta (fun _ => 1) interior ∅ * currentSum G beta (fun _ => 1) ∅) := by
-- proof
  apply StatMech.FrontierB.beta_mul_boundarySource_twoPoint_gap_le_exteriorConnection_ratio G beta hbeta interior e hleft hright


-- created on 2026-10-23
