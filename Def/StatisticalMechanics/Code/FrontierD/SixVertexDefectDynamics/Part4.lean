/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexForwardMoveEmbedding
    {N n : Nat} (x : SixVertexSector N n) (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j) :
    Fin n ↪o Fin N :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(sixVertexSectorPosition x i).val + a i, hbound i⟩)
    (by
      intro i j hij
      exact hmono i j hij)


def sixVertexForwardMoveSector
    {N n : Nat} (x : SixVertexSector N n) (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j) :
    SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv
    (sixVertexForwardMoveEmbedding x a hbound hmono)

end
end StatMech.FrontierD
