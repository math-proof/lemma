module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactVariation.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactEnergy
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareRadialPatchWindowCell
    (m baseI baseJ R : Nat)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p : IsingLeapfrogBox R) : FKIsingSquareRadialPatchInteriorCell m :=
  (⟨baseI + p.1.1, by have := p.1.2; omega⟩,
    ⟨baseJ + p.2.1, by have := p.2.2; omega⟩)

end
end StatMech.Universality
