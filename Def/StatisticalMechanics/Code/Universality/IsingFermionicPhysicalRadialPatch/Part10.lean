/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

def fkIsingSquareRadialPatchPrimalNodeVertex
    (n m : Nat) (hm : m ≤ n) :
    FKIsingSquareRadialPatchPrimalNode m → (fkSquareBoxPlanar n).V :=
  fun p ↦ fkIsingSquareRadialPatchVertex n m hm p.1.1 p.1.2

end
end StatMech.Universality
