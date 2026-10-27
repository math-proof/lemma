import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFirstGKSDrop
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamFirstComponentFiber_remainder_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDrop.lean)
-/
@[path]
private lemma grahamFirstComponentFiber_remainder_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {i j : V}
-- given
  (J : Sym2 V -> Real)
  (hi : i ∉ S)
  (hj : j ∉ S) :
-- imply
  grahamFirstComponentFiber G beta J S i {i, j} ∅ = currentSum G beta (couplingIn J S) ∅ ^ 2 * grahamFirstComponentContext G beta J S i j := by
-- proof
  apply StatMech.FrontierA.grahamFirstComponentFiber_remainder_factor G beta J S hi hj

/--
[grahamFirstComponentFiber_mixed_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDrop.lean)
-/
@[path]
private lemma grahamFirstComponentFiber_mixed_factor_eq
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
  grahamFirstComponentFiber G beta J S i {i, j} {k, l} = currentSum G beta (couplingIn J S) ∅ * currentSum G beta (couplingIn J S) {k, l} * grahamFirstComponentContext G beta J S i j := by
-- proof
  apply StatMech.FrontierA.grahamFirstComponentFiber_mixed_factor G beta J S hi hj hk hl

/--
[grahamFirstComponentGKSDrop_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDrop.lean)
-/
@[path]
private lemma grahamFirstComponentGKSDrop_identity_eq
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
  currentSum G beta J {k, l} * grahamFirstComponentFiber G beta J S i {i, j} ∅ - currentSum G beta J ∅ * grahamFirstComponentFiber G beta J S i {i, j} {k, l} = currentSum G beta J ∅ * grahamFirstComponentFiber G beta J S i {i, j} ∅ * (expectationJ G beta J {k, l} - expectationJ G beta (couplingIn J S) {k, l}) := by
-- proof
  apply StatMech.FrontierA.grahamFirstComponentGKSDrop_identity G beta J S hi hj hk hl

/--
[grahamFirstComponentGKSDrop_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDrop.lean)
-/
@[path]
private lemma grahamFirstComponentGKSDrop_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hi : i ∉ S)
  (hj : j ∉ S)
  (hk : k ∈ S)
  (hl : l ∈ S) :
-- imply
  0 ≤ currentSum G beta J {k, l} * grahamFirstComponentFiber G beta J S i {i, j} ∅ - currentSum G beta J ∅ * grahamFirstComponentFiber G beta J S i {i, j} {k, l} := by
-- proof
  apply StatMech.FrontierA.grahamFirstComponentGKSDrop_nonneg G beta J hbeta hJ S hi hj hk hl


-- created on 2026-10-23
