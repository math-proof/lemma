/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeInsertion
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialToggle
open Finset


namespace StatMech.FrontierD

@[simp] theorem fkMedialTogglePairingAt_self {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialTogglePairingAt pairing v v = !pairing v := by
  simp [fkMedialTogglePairingAt]

theorem fkMedialTogglePairingAt_of_ne {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) {v w : T.Vertex} (h : w ≠ v) :
    fkMedialTogglePairingAt pairing v w = pairing w := by
  simp [fkMedialTogglePairingAt, h]


end StatMech.FrontierD
