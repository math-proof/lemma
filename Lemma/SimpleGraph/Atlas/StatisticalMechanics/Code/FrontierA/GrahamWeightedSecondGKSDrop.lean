import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedSecondGKSDrop
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamSecondComponentFiber_remainder_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDrop.lean)
-/
@[path]
private lemma grahamSecondComponentFiber_remainder_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {k l : V}
-- given
  (J : Sym2 V -> Real)
  (hk : k ∉ S)
  (hl : l ∉ S) :
-- imply
  grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) = currentSum G beta (couplingIn J S) ∅ ^ 2 * grahamSecondComponentContext G beta J S k l := by
-- proof
  apply StatMech.FrontierA.grahamSecondComponentFiber_remainder_factor G beta J S hk hl

/--
[grahamSecondComponentFiber_mixed_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDrop.lean)
-/
@[path]
private lemma grahamSecondComponentFiber_mixed_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m)
  (hi : i ∈ S)
  (hj : j ∈ S)
  (hm : m ∈ S)
  (hk : k ∉ S)
  (hl : l ∉ S) :
-- imply
  grahamSecondComponentFiber G beta J S k {i, j} {k, l} (fun n => CurrentConnected G n i m) = currentSum G beta (couplingIn J S) {j, m} * currentSum G beta (couplingIn J S) {i, m} * grahamSecondComponentContext G beta J S k l := by
-- proof
  apply StatMech.FrontierA.grahamSecondComponentFiber_mixed_factor G beta J S hij hik hil him hjk hjl hjm hkl hkm hlm hi hj hm hk hl

/--
[grahamSecondComponentGKSDrop_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDrop.lean)
-/
@[path]
private lemma grahamSecondComponentGKSDrop_identity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m)
  (hi : i ∈ S)
  (hj : j ∈ S)
  (hm : m ∈ S)
  (hk : k ∉ S)
  (hl : l ∉ S) :
-- imply
  (currentSum G beta J {i, m} * currentSum G beta J {j, m}) * grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) - currentSum G beta J ∅ ^ 2 * grahamSecondComponentFiber G beta J S k {i, j} {k, l} (fun n => CurrentConnected G n i m) = currentSum G beta J ∅ ^ 2 * grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) * (expectationJ G beta J {i, m} * expectationJ G beta J {j, m} - expectationJ G beta (couplingIn J S) {i, m} * expectationJ G beta (couplingIn J S) {j, m}) := by
-- proof
  apply StatMech.FrontierA.grahamSecondComponentGKSDrop_identity G beta J S hij hik hil him hjk hjl hjm hkl hkm hlm hi hj hm hk hl

/--
[grahamRestrictedCorrelationProduct_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDrop.lean)
-/
@[path]
private lemma grahamRestrictedCorrelationProduct_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {i j m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  expectationJ G beta (couplingIn J S) {i, m} * expectationJ G beta (couplingIn J S) {j, m} ≤ expectationJ G beta J {i, m} * expectationJ G beta J {j, m} := by
-- proof
  apply StatMech.FrontierA.grahamRestrictedCorrelationProduct_le G beta J hbeta hJ S i j m

/--
[grahamSecondComponentGKSDrop_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedSecondGKSDrop.lean)
-/
@[path]
private lemma grahamSecondComponentGKSDrop_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m)
  (hi : i ∈ S)
  (hj : j ∈ S)
  (hm : m ∈ S)
  (hk : k ∉ S)
  (hl : l ∉ S) :
-- imply
  0 ≤ (currentSum G beta J {i, m} * currentSum G beta J {j, m}) * grahamSecondComponentFiber G beta J S k {k, l} ∅ (fun _ => True) - currentSum G beta J ∅ ^ 2 * grahamSecondComponentFiber G beta J S k {i, j} {k, l} (fun n => CurrentConnected G n i m) := by
-- proof
  apply StatMech.FrontierA.grahamSecondComponentGKSDrop_nonneg G beta J hbeta hJ S hij hik hil him hjk hjl hjm hkl hkm hlm hi hj hm hk hl


-- created on 2026-10-23
