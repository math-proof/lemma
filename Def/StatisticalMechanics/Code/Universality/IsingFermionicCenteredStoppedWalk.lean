/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredStoppedWalk


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
    (n baseI baseJ R : Nat) (hn : 0 < n)
    (hfitI : baseI + R + 1 < 2 * n)
    (hfitJ : baseJ + R + 1 < 2 * n) :
    IsingLeapfrogBox R → Complex :=
  fun p ↦ fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
    ⟨baseI + p.1.1, by have := p.1.2; omega⟩
    ⟨baseJ + p.2.1, by have := p.2.2; omega⟩


end
end StatMech.Universality
