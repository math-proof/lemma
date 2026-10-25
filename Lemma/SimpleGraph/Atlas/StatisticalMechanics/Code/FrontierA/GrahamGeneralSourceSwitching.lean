import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGeneralSourceSwitching
open Finset SimpleGraph Classical StatMech StatMech.FrontierA StatMech.FrontierA.GrahamGeneralSourceSwitching


/--
[edgecopy_sourcePair_shift_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGeneralSourceSwitching.lean)
-/
@[path]
private lemma edgecopy_sourcePair_shift_of_connected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
  {u v : V}
-- given
  (m : ↑G.edgeFinset -> Nat)
  (huv : u ≠ v)
  (hconn : RandomCurrent.connK (endsM G m) (Finset.univ : Finset (Copy G m)) u v) :
-- imply
  (∑ K : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) K = A then (1 : Real) else 0) * (if RandomCurrent.sources (endsM G m) ((Finset.univ : Finset (Copy G m)) \ K) = B then 1 else 0)) = ∑ K : Finset (Copy G m), (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : Real) else 0) * (if RandomCurrent.sources (endsM G m) ((Finset.univ : Finset (Copy G m)) \ K) = B ∆ {u, v} then 1 else 0) := by
-- proof
  apply StatMech.FrontierA.GrahamGeneralSourceSwitching.edgecopy_sourcePair_shift_of_connected G m A B huv hconn

/--
[gatedSourcePairSum_shift_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGeneralSourceSwitching.lean)
-/
@[path]
private lemma gatedSourcePairSum_shift_connected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
  {u v : V}
  [DecidablePred P]
-- given
  (J : Sym2 V -> Real)
  (huv : u ≠ v)
  (P : Current V -> Prop) :
-- imply
  gatedSourcePairSum G beta J A B (fun n => P n ∧ CurrentConnected G n u v) = gatedSourcePairSum G beta J (A ∆ {u, v}) (B ∆ {u, v}) (fun n => P n ∧ CurrentConnected G n u v) := by
-- proof
  apply StatMech.FrontierA.gatedSourcePairSum_shift_connected G beta J A B huv P


-- created on 2026-10-23
