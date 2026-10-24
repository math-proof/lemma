import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentContinuityFiniteSwitching
open StatMech StatMech.FrontierB


/--
[boundarySourceGatedPairSum_empty_pair_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFiniteSwitching.lean)
-/
@[path]
private lemma boundarySourceGatedPairSum_empty_pair_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {interior : Finset V}
  {u v : V}
  [DecidablePred P]
-- given
  (J : Sym2 V -> Real)
  (huv : u ≠ v)
  (hu : u ∈ interior)
  (hv : v ∈ interior)
  (P : Current V -> Prop) :
-- imply
  boundarySourceGatedPairSum G beta J interior ∅ {u, v} P = boundarySourceGatedPairSum G beta J interior {u, v} ∅ (fun m => P m ∧ CurrentConnected G m u v) := by
-- proof
  apply StatMech.FrontierB.boundarySourceGatedPairSum_empty_pair_switching G beta J interior huv hu hv P

/--
[boundarySourceGatedPairSum_true_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFiniteSwitching.lean)
-/
@[path]
private lemma boundarySourceGatedPairSum_true_eq_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {interior internalSources exactSecondSources : Finset V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  boundarySourceGatedPairSum G beta J interior internalSources exactSecondSources (fun _ => True) = boundarySourceCurrentSum G beta J interior internalSources * currentSum G beta J exactSecondSources := by
-- proof
  apply StatMech.FrontierB.boundarySourceGatedPairSum_true_eq_mul G beta J interior internalSources exactSecondSources

/--
[boundarySourceGatedPairSum_conn_add_notConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFiniteSwitching.lean)
-/
@[path]
private lemma boundarySourceGatedPairSum_conn_add_notConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {interior internalSources exactSecondSources : Finset V}
  {u v : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  boundarySourceGatedPairSum G beta J interior internalSources exactSecondSources (fun m => CurrentConnected G m u v) + boundarySourceGatedPairSum G beta J interior internalSources exactSecondSources (fun m => ¬ CurrentConnected G m u v) = boundarySourceGatedPairSum G beta J interior internalSources exactSecondSources (fun _ => True) := by
-- proof
  apply StatMech.FrontierB.boundarySourceGatedPairSum_conn_add_notConn G beta J interior internalSources exactSecondSources u v

/--
[boundarySource_twoPoint_gap_eq_notConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFiniteSwitching.lean)
-/
@[path]
private lemma boundarySource_twoPoint_gap_eq_notConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {interior : Finset V}
  {u v : V}
-- given
  (J : Sym2 V -> Real)
  (huv : u ≠ v)
  (hu : u ∈ interior)
  (hv : v ∈ interior) :
-- imply
  boundarySourceCurrentSum G beta J interior {u, v} * currentSum G beta J ∅ - boundarySourceCurrentSum G beta J interior ∅ * currentSum G beta J {u, v} = boundarySourceGatedPairSum G beta J interior {u, v} ∅ (fun m => ¬ CurrentConnected G m u v) := by
-- proof
  apply StatMech.FrontierB.boundarySource_twoPoint_gap_eq_notConnected G beta J interior huv hu hv

/--
[exists_ne_source_currentConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFiniteSwitching.lean)
-/
@[path]
private lemma exists_ne_source_currentConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : EdgeCurrent G}
  {u : V}
-- given
  (hu : u ∈ sources G (ofEdgeFun G m)) :
-- imply
  ∃ z : V, z ∈ sources G (ofEdgeFun G m) ∧ z ≠ u ∧ CurrentConnected G (ofEdgeFun G m) u z := by
-- proof
  apply StatMech.FrontierB.exists_ne_source_currentConnected G m u hu

/--
[currentConnected_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFiniteSwitching.lean)
-/
@[path]
private lemma currentConnected_add_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m n : EdgeCurrent G}
  {x y : V}
-- given
  (h : CurrentConnected G (ofEdgeFun G m) x y) :
-- imply
  CurrentConnected G (ofEdgeFun G (fun e => m e + n e)) x y := by
-- proof
  apply StatMech.FrontierB.currentConnected_add_right G m n h

/--
[boundarySource_notConnected_reaches_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFiniteSwitching.lean)
-/
@[path]
private lemma boundarySource_notConnected_reaches_exterior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {interior : Finset V}
  {u v : V}
  {m n : EdgeCurrent G}
-- given
  (huv : u ≠ v)
  (hsrc : sources G (ofEdgeFun G m) ∩ interior = {u, v})
  (hnot : ¬ CurrentConnected G (ofEdgeFun G (fun e => m e + n e)) u v) :
-- imply
  ∃ z : V, z ∉ interior ∧ CurrentConnected G (ofEdgeFun G (fun e => m e + n e)) u z := by
-- proof
  apply StatMech.FrontierB.boundarySource_notConnected_reaches_exterior G interior huv m n hsrc hnot


-- created on 2026-10-23
