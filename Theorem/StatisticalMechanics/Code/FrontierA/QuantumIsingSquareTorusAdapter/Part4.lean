/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


@[simp] theorem quantumIsingSquareConfigEquiv_apply
    (L : Nat) [NeZero L]
    (omega : Fin L → QuantumIsingChainConfig L) (k i : Fin L) :
    quantumIsingSquareConfigEquiv L omega
        (ZMod.finEquiv L i, ZMod.finEquiv L k) = omega k i := by
  simp [quantumIsingSquareConfigEquiv]

theorem finEquiv_quantumIsingCyclicSucc
    (L : Nat) [NeZero L] (i : Fin L) :
    ZMod.finEquiv L (quantumIsingCyclicSucc i) =
      ZMod.finEquiv L i + 1 := by
  rw [quantumIsingCyclicSucc_eq_add_one]
  simpa using (ZMod.finEquiv L).map_add i 1


end StatMech.FrontierA
