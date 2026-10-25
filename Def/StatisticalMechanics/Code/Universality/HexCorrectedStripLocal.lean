/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCyclicAtomSupport
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointPieceRigidity
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointTripletOrbit
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripStartReturn
import Instance.StatisticalMechanics.Code.Universality.HexCorrectedStripLocal


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

def HexCSTerminalSelectedSide (t h : ℤ) (tail : List ℤ) : Prop :=
  let dirs := hexCSBrickDirections (h + t) tail
  let d : Fin dirs.length → Fin 4 := fun i => dirs.get i
  (t = 1 → Orientation.leftParity d 0 = 1) ∧
    (t = -1 → Orientation.leftParity d 0 ≠ 1)

def hexCSRightCell : Fin 4 → ℤ × ℤ → ℤ × ℤ
  | 0, p => (p.1, p.2 - 1)
  | 1, p => p
  | 2, p => (p.1 - 1, p.2)
  | 3, p => (p.1 - 1, p.2 - 1)


end
end StatMech.Universality
