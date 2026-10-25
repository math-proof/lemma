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
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def quantumIsingSquareTrotterEnergy
    (beta h : Real) (L : Nat)
    (omega : Fin L → QuantumIsingChainConfig L) : Real :=
  (∑ k : Fin L,
      beta / (4 * L) * quantumIsingChainInteraction L (omega k)) +
    ∑ k : Fin L, ∑ i : Fin L,
      quantumIsingVerticalCoupling beta h L *
        (quantumIsingSpinSign (omega k i) *
          quantumIsingSpinSign
            (omega (quantumIsingCyclicSucc k) i))


end StatMech.FrontierA
