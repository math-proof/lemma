/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledLimitingRoot (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) : Real :=
  (2 * Real.pi * sixVertexCentralQuantumNumber j) /
    (((k + 1) + (k + 1) : Nat) : Real)


def sixVertexHalfFilledLimitingPhase (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) : Complex :=
  sixVertexBethePhase (sixVertexHalfFilledLimitingRoot k j)

end
end StatMech.FrontierD
