/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part8


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

def fkIsingSquareRadialPatchPrimitive
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real :=
  isingRectanglePrimitive
    (fkIsingSquareRadialPatchHorizontalSignedIncrement n m hn hm hmpos)
    (fkIsingSquareRadialPatchVerticalSignedIncrement n m hn hm hmpos)

end
end StatMech.Universality
