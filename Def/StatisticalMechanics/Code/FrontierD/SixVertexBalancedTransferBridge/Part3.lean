/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part2
open Finset Matrix


namespace StatMech.FrontierD

def svRowPrefixForward {N : Nat} (x y : SixVertexRow N) : Prop :=
  ∀ k, svRowPrefixCount y k ≤ svRowPrefixCount x k ∧
    svRowPrefixCount x k ≤ svRowPrefixCount y k + 1

def svRowSectorAt {N n : Nat} (x : SixVertexRow N)
    (hx : sixVertexUpCount x = n) : SixVertexSector N n :=
  ⟨({i | x i} : Finset (Fin N)), hx⟩

end StatMech.FrontierD
