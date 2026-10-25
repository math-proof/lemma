import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponentResummation.Part2
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[grahamComponentPairMass_eq_gatedSourcePairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean)
-/
@[path]
private lemma grahamComponentPairMass_eq_gatedSourcePairSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {g : V}
  {A : Finset V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamComponentPairMass G beta J S g A = gatedSourcePairSum G beta J A ∅ (fun m => notConnComp G m g = S) := by
-- proof
  apply StatMech.FrontierA.grahamComponentPairMass_eq_gatedSourcePairSum G beta J S g A

/--
[grahamComponentPairMass_pair_eq_restricted_mul_vacuum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean)
-/
@[path]
private lemma grahamComponentPairMass_pair_eq_restricted_mul_vacuum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {g k l : V}
-- given
  (J : Sym2 V -> Real)
  (hg : g ∉ S)
  (hk : k ∈ S)
  (hl : l ∈ S) :
-- imply
  grahamComponentPairMass G beta J S g {k, l} = expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l} * grahamComponentPairMass G beta J S g ∅ := by
-- proof
  apply StatMech.FrontierA.grahamComponentPairMass_pair_eq_restricted_mul_vacuum G beta J S g k l hg hk hl

/--
[grahamDisconnectedPairMass_eq_restrictedVacuumComponentMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean)
-/
@[path]
private lemma grahamDisconnectedPairMass_eq_restrictedVacuumComponentMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  grahamDisconnectedPairMass G beta J g k l = grahamRestrictedVacuumComponentMass G beta J g k l := by
-- proof
  apply StatMech.FrontierA.grahamDisconnectedPairMass_eq_restrictedVacuumComponentMass G beta J g k l

/--
[graham_full_mul_vacuum_sub_disconnected_eq_gksDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean)
-/
@[path]
private lemma graham_full_mul_vacuum_sub_disconnected_eq_gksDrop_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  expectationJ G beta J {k, l} * (∑ S ∈ grahamAdmissibleComponentComplements g k l, grahamComponentPairMass G beta J S g ∅) - grahamDisconnectedPairMass G beta J g k l = ∑ S ∈ grahamAdmissibleComponentComplements g k l, grahamComponentPairMass G beta J S g ∅ * (expectationJ G beta J {k, l} - expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l}) := by
-- proof
  apply StatMech.FrontierA.graham_full_mul_vacuum_sub_disconnected_eq_gksDrop G beta J g k l

/--
[grahamComponentGKSDifference_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean)
-/
@[path]
private lemma grahamComponentGKSDifference_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  0 <= expectationJ G beta J {k, l} - expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l} := by
-- proof
  apply StatMech.FrontierA.grahamComponentGKSDifference_nonneg G beta J hbeta hJ S k l

/--
[grahamComponentPairMass_vacuum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean)
-/
@[path]
private lemma grahamComponentPairMass_vacuum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {g : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  0 <= grahamComponentPairMass G beta J S g ∅ := by
-- proof
  apply StatMech.FrontierA.grahamComponentPairMass_vacuum_nonneg G beta J hbeta hJ S g

/--
[grahamComponentGKSDrop_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean)
-/
@[path]
private lemma grahamComponentGKSDrop_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  0 <= ∑ S ∈ grahamAdmissibleComponentComplements g k l, grahamComponentPairMass G beta J S g ∅ * (expectationJ G beta J {k, l} - expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l}) := by
-- proof
  apply StatMech.FrontierA.grahamComponentGKSDrop_nonneg G beta J hbeta hJ g k l


-- created on 2026-10-23
