/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part13


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

noncomputable def fkIsingSquareGrowingRadialPrimalPrimitive
    (m : Nat → Nat) (hm : ∀ n, m n ≤ n) (base : Nat → Real) :
    ∀ n, (fkSquareBoxPlanar n).V → Real :=
  fun n ↦ if hmn : 0 < m n then
    fkIsingSquareRadialPatchPrimalPrimitiveExtension
      n (m n) (lt_of_lt_of_le hmn (hm n)) (hm n) hmn (base n)
  else fun _ ↦ 0

end
end StatMech.Universality
