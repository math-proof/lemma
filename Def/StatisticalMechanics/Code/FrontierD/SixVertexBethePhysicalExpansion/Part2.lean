/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheCollision {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) (i : Fin (n + 1)) : Prop :=
  q i = x i /\
    q (finRotate (n + 1) i) =
      sixVertexBetheShiftCoordinates N x (finRotate (n + 1) i)


def sixVertexBetheCollisionSet {n : Nat} (N : Nat)
    (x q : Fin (n + 1) -> Int) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (sixVertexBetheCollision N x q)

end
end StatMech.FrontierD
