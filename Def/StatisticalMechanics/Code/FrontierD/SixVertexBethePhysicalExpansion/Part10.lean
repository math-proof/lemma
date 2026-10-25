/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part9
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheUnshiftCoordinates {n : Nat} (N : Nat)
    (q : Fin (n + 1) -> Int) : Fin (n + 1) -> Int :=
  Fin.lastCases (q 0 + N) (fun i => q i.succ)

end
end StatMech.FrontierD
