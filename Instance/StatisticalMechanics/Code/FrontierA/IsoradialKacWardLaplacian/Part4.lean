/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part5


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


noncomputable instance finiteCRSFAtomicCycleFintype (next : V -> V) :
    Fintype (finiteCRSFAtomicCycle next) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun cycle : Equiv.Perm V =>
      cycle.IsCycle ∧ ∀ v ∈ cycle.support, cycle v = next v) (by
        intro cycle
        simp)


end StatMech.FrontierA
