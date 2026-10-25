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
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def quantumIsingSquareConfigEquiv
    (L : Nat) [NeZero L] :
    (Fin L → QuantumIsingChainConfig L) ≃
      ConfigSpace (ZMod L × ZMod L) where
  toFun omega p :=
    omega ((ZMod.finEquiv L).symm p.2) ((ZMod.finEquiv L).symm p.1)
  invFun sigma k i := sigma (ZMod.finEquiv L i, ZMod.finEquiv L k)
  left_inv omega := by
    funext k i
    simp
  right_inv sigma := by
    funext p
    simp

end StatMech.FrontierA
