/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDominationInner.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Def.StatisticalMechanics.Code.FK.WiredDominationInner
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem inducedBcZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    0 < inducedBcZ G C p q F ψ :=
  Finset.sum_pos (fun ρ _ => bcWeight_pos G C hp hp1 hq ρ) ⟨ψ, self_mem_condFibre F ψ⟩

theorem inducedBcZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    inducedBcZ G C p q F ψ ≠ 0 :=
  (inducedBcZ_pos G C hp hp1 hq F ψ).ne'


end FK
end StatMech
