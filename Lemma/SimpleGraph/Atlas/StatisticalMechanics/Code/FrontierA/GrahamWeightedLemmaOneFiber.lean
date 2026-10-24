import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneFiber
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamSourcePairComponentFiber_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiber.lean)
-/
@[path]
private lemma grahamSourcePairComponentFiber_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {m : V}
  {A C : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hm : m ∉ S)
  (hA : A ⊆ S)
  (hC : C ⊆ S) :
-- imply
  grahamSourcePairComponentFiber G beta J S m A C = currentSum G beta (couplingIn J S) A * currentSum G beta (couplingIn J S) C * grahamComponentExteriorContext G beta J S m := by
-- proof
  apply StatMech.FrontierA.grahamSourcePairComponentFiber_factor G beta J S m hm A C hA hC

/--
[grahamSourcePairComponentFiber_mixed_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiber.lean)
-/
@[path]
private lemma grahamSourcePairComponentFiber_mixed_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hm : m ∉ S)
  (hj : j ∈ S)
  (hk : k ∈ S)
  (hl : l ∈ S) :
-- imply
  grahamSourcePairComponentFiber G beta J S m {j, k} {k, l} = currentSum G beta (couplingIn J S) {j, k} * currentSum G beta (couplingIn J S) {k, l} * grahamComponentExteriorContext G beta J S m := by
-- proof
  apply StatMech.FrontierA.grahamSourcePairComponentFiber_mixed_factor G beta J S hm hj hk hl

/--
[grahamSourcePairComponentFiber_left_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiber.lean)
-/
@[path]
private lemma grahamSourcePairComponentFiber_left_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {j k m : V}
-- given
  (J : Sym2 V -> Real)
  (hm : m ∉ S)
  (hj : j ∈ S)
  (hk : k ∈ S) :
-- imply
  grahamSourcePairComponentFiber G beta J S m {j, k} ∅ = currentSum G beta (couplingIn J S) {j, k} * currentSum G beta (couplingIn J S) ∅ * grahamComponentExteriorContext G beta J S m := by
-- proof
  apply StatMech.FrontierA.grahamSourcePairComponentFiber_left_factor G beta J S hm hj hk

/--
[grahamSourcePairComponentFiber_right_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiber.lean)
-/
@[path]
private lemma grahamSourcePairComponentFiber_right_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hm : m ∉ S)
  (hk : k ∈ S)
  (hl : l ∈ S) :
-- imply
  grahamSourcePairComponentFiber G beta J S m {k, l} ∅ = currentSum G beta (couplingIn J S) {k, l} * currentSum G beta (couplingIn J S) ∅ * grahamComponentExteriorContext G beta J S m := by
-- proof
  apply StatMech.FrontierA.grahamSourcePairComponentFiber_right_factor G beta J S hm hk hl

/--
[grahamSourcePairComponentFiber_vacuum_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiber.lean)
-/
@[path]
private lemma grahamSourcePairComponentFiber_vacuum_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {m : V}
-- given
  (J : Sym2 V -> Real)
  (hm : m ∉ S) :
-- imply
  grahamSourcePairComponentFiber G beta J S m ∅ ∅ = currentSum G beta (couplingIn J S) ∅ ^ 2 * grahamComponentExteriorContext G beta J S m := by
-- proof
  apply StatMech.FrontierA.grahamSourcePairComponentFiber_vacuum_factor G beta J S hm

/--
[grahamSourcePairComponentFiber_det_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiber.lean)
-/
@[path]
private lemma grahamSourcePairComponentFiber_det_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hm : m ∉ S)
  (hj : j ∈ S)
  (hk : k ∈ S)
  (hl : l ∈ S) :
-- imply
  grahamSourcePairComponentFiber G beta J S m {j, k} {k, l} * grahamSourcePairComponentFiber G beta J S m ∅ ∅ = grahamSourcePairComponentFiber G beta J S m {j, k} ∅ * grahamSourcePairComponentFiber G beta J S m {k, l} ∅ := by
-- proof
  apply StatMech.FrontierA.grahamSourcePairComponentFiber_det_zero G beta J S hm hj hk hl


-- created on 2026-10-23
