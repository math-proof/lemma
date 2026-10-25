/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part11


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

noncomputable def fkIsingSquareRadialPatchPrimalPrimitiveExtension
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) : (fkSquareBoxPlanar n).V → Real :=
  Function.extend
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm)
    (fun p ↦ base + fkIsingSquareRadialPatchPrimitive
      n m hn hm hmpos p.1.1.1 p.1.2.1)
    (fun _ ↦ 0)

end
end StatMech.Universality
