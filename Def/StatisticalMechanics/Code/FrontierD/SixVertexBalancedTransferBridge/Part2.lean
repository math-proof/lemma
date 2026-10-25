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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge
open Finset Matrix


namespace StatMech.FrontierD

def svHorizontalIncomingCount {N : Nat} (hN : 0 < N)
    (x y h : SixVertexRow N) (i : Fin N) : Nat :=
  (x i).toNat + (!y i).toNat +
    (h (SixVertexArrows.cyclicPred hN i)).toNat + (!h i).toNat

def svHorizontalIce {N : Nat} (hN : 0 < N)
    (x y h : SixVertexRow N) : Prop :=
  ∀ i, svHorizontalIncomingCount hN x y h i = 2

def svFinLast {N : Nat} (hN : 0 < N) : Fin N :=
  ⟨N - 1, Nat.sub_lt hN (by omega)⟩

end StatMech.FrontierD
