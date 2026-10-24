import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponentPartition
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamDisconnectedPairMass_eq_sourcePairDisconnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentPartition.lean)
-/
@[path]
private lemma grahamDisconnectedPairMass_eq_sourcePairDisconnSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g k l : V}
-- given
  (J : Sym2 V -> Real)
  (hkl : k ≠ l) :
-- imply
  grahamDisconnectedPairMass G beta J g k l = sourcePairDisconnSum G beta J {k, l} ∅ g k := by
-- proof
  apply StatMech.FrontierA.grahamDisconnectedPairMass_eq_sourcePairDisconnSum G beta J hkl

/--
[sourcePairDisconnSum_eq_restrictedVacuumComponentMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentPartition.lean)
-/
@[path]
private lemma sourcePairDisconnSum_eq_restrictedVacuumComponentMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g k l : V}
-- given
  (J : Sym2 V -> Real)
  (hkl : k ≠ l) :
-- imply
  sourcePairDisconnSum G beta J {k, l} ∅ g k = grahamRestrictedVacuumComponentMass G beta J g k l := by
-- proof
  apply StatMech.FrontierA.sourcePairDisconnSum_eq_restrictedVacuumComponentMass G beta J hkl

/--
[graham_full_mul_vacuum_sub_sourcePairDisconn_eq_gksDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentPartition.lean)
-/
@[path]
private lemma graham_full_mul_vacuum_sub_sourcePairDisconn_eq_gksDrop_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g k l : V}
-- given
  (J : Sym2 V -> Real)
  (hkl : k ≠ l) :
-- imply
  expectationJ G beta J {k, l} * (∑ S ∈ grahamAdmissibleComponentComplements g k l, grahamComponentPairMass G beta J S g ∅) - sourcePairDisconnSum G beta J {k, l} ∅ g k = ∑ S ∈ grahamAdmissibleComponentComplements g k l, grahamComponentPairMass G beta J S g ∅ * (expectationJ G beta J {k, l} - expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l}) := by
-- proof
  apply StatMech.FrontierA.graham_full_mul_vacuum_sub_sourcePairDisconn_eq_gksDrop G beta J hkl


-- created on 2026-10-23
