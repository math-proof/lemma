module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part3
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

def sixVertexRectangleTileBlocksBoundaryFiber
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)} :
    SixVertexRectangleBlockCopies ξ a b →
      SixVertexRectangleBoundaryFiber
        (sixVertexToroidalRectangleBoundary
          (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ)) :=
  fun ω => ⟨sixVertexRectangleTileBlocks ω,
    sixVertexRectangleTileBlocks_boundary ω⟩

end StatMech.FrontierD
