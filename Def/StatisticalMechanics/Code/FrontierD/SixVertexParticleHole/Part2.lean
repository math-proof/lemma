/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part2
open Finset Matrix


namespace StatMech.FrontierD

def SixVertexSectorPrefixForward {N n : ℕ}
    (x y : SixVertexSector N n) : Prop :=
  ∀ k, sixVertexSectorPrefixCount y k ≤ sixVertexSectorPrefixCount x k ∧
    sixVertexSectorPrefixCount x k ≤ sixVertexSectorPrefixCount y k + 1

end StatMech.FrontierD
