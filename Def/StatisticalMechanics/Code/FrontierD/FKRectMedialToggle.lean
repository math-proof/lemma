/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeInsertion
open Finset


namespace StatMech.FrontierD

def fkMedialTogglePairingAt {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    FKMedialLoopPairing T :=
  fun w => if w = v then !pairing w else pairing w

end StatMech.FrontierD
