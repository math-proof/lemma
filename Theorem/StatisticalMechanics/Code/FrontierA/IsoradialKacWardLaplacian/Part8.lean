/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part9


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

theorem restrictedPerm_support {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.restrictedPerm.support = Finset.univ := by
  ext v
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
  intro hfixed
  have hnext : next v = v := by
    exact congrArg Subtype.val hfixed
  exact S.noFixed v v.property hnext


end finiteCRSFCycleSupport
end StatMech.FrontierA
