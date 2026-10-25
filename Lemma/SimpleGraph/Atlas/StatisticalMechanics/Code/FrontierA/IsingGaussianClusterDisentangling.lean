import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterDisentangling
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[finiteTree_component_sourceReplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterDisentangling.lean)
-/
@[path]
private lemma finiteTree_component_sourceReplacement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hi : i ∉ S)
  (hj : j ∉ S)
  (hk : k ∈ S)
  (hl : l ∈ S) :
-- imply
  grahamFirstComponentFiber G beta J S i {i, j} {k, l} = expectationJ G beta (couplingIn J S) {k, l} * grahamFirstComponentFiber G beta J S i {i, j} ∅ := by
-- proof
  apply StatMech.FrontierA.finiteTree_component_sourceReplacement G beta J S hi hj hk hl

/--
[finiteTree_mixedDisconnection_eq_componentReplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterDisentangling.lean)
-/
@[path]
private lemma finiteTree_mixedDisconnection_eq_componentReplacement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hkl : k ≠ l) :
-- imply
  sourcePairDisconnSum G beta J {i, j} {k, l} i k = ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k, expectationJ G beta (couplingIn J S) {k, l} * grahamFirstComponentFiber G beta J S i {i, j} ∅ := by
-- proof
  apply StatMech.FrontierA.finiteTree_mixedDisconnection_eq_componentReplacement G beta J hij hkl

/--
[finiteTree_componentReplacement_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterDisentangling.lean)
-/
@[path]
private lemma finiteTree_componentReplacement_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  0 <= expectationJ G beta (couplingIn J S) {k, l} * grahamFirstComponentFiber G beta J S i {i, j} ∅ := by
-- proof
  apply StatMech.FrontierA.finiteTree_componentReplacement_nonneg G beta J hbeta hJ S i j k l


-- created on 2026-10-23
