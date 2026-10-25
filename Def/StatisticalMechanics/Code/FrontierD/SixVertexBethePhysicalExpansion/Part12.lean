/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part11
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheInteriorSet {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i =>
    q i ≠ sixVertexBetheShiftCoordinates N x i ∧ q i ≠ x i

end
end StatMech.FrontierD
