/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryRadialPatchFullObservableExtension
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) : Nat → Nat → Complex :=
  fun i j ↦
    if hi : i < m then
      if hj : j < m then
        fkIsingSquareBoundaryRadialPatchFullObservable
          n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0

end
end StatMech.Universality
