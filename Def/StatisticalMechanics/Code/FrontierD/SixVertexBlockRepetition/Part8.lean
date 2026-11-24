module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part8
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

def sixVertexRectangleStraightExtendBoundaryFiber
    {N M r q : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (z : Fin r → Bool) :
    SixVertexRectangleBoundaryFiber
        (sixVertexToroidalRectangleBoundary ξ) →
      SixVertexRectangleBoundaryFiber
        (sixVertexToroidalRectangleBoundary
          (sixVertexStraightExtendedToroidalBoundary q ξ z)) :=
  fun ω => ⟨sixVertexRectangleStraightExtend (q := q) z ω.1,
    sixVertexRectangleStraightExtend_boundary z ω⟩

end StatMech.FrontierD
