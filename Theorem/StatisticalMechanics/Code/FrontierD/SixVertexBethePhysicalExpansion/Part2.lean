/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_sixVertexBetheCollisionSet {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) (i : Fin (n + 1)) :
    i ∈ sixVertexBetheCollisionSet N x q ↔
      sixVertexBetheCollision N x q i := by
  simp [sixVertexBetheCollisionSet]


end
end StatMech.FrontierD
