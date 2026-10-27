import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponentPartitionFiber
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamComponentPairMass_eq_gatedDisconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentPartitionFiber.lean)
-/
@[path]
private lemma grahamComponentPairMass_eq_gatedDisconnection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g k l : V}
  {S : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hkl : k ≠ l)
  (hS : S ∈ grahamAdmissibleComponentComplements g k l) :
-- imply
  grahamComponentPairMass G beta J S g {k, l} = gatedSourcePairSum G beta J {k, l} ∅ (fun n => notConnComp G n g = S ∧ ¬ CurrentConnected G n g k) := by
-- proof
  apply StatMech.FrontierA.grahamComponentPairMass_eq_gatedDisconnection G beta J hkl S hS

/--
[grahamGatedDisconnection_eq_zero_of_not_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentPartitionFiber.lean)
-/
@[path]
private lemma grahamGatedDisconnection_eq_zero_of_not_admissible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g k l : V}
  {S : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hkl : k ≠ l)
  (hS : S ∉ grahamAdmissibleComponentComplements g k l) :
-- imply
  gatedSourcePairSum G beta J {k, l} ∅ (fun n => notConnComp G n g = S ∧ ¬ CurrentConnected G n g k) = 0 := by
-- proof
  apply StatMech.FrontierA.grahamGatedDisconnection_eq_zero_of_not_admissible G beta J hkl S hS


-- created on 2026-10-23
