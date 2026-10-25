/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part10
open Finset


namespace StatMech.FrontierD

def sixVertexRectangleStraightExtendBalancedFibers
    {N M r : ℕ} (hN : Even (N + 1)) (hr : Even r) (q : ℕ) :
    SixVertexRectangleBalancedBoundaryFibers (N + 1) (M + 1) →
      SixVertexRectangleBalancedBoundaryFibers
        ((N + 1) + r) ((M + 1) + q) :=
  fun ξω =>
    ⟨⟨sixVertexStraightExtendedToroidalBoundary q ξω.1.1
        (sixVertexHalfFilledRow r),
      sixVertexStraightExtendedToroidalBoundary_balanced
        hN hr q ξω.1.1 ξω.1.2⟩,
      sixVertexRectangleStraightExtendBoundaryFiber
        (q := q) (ξ := ξω.1.1) (sixVertexHalfFilledRow r) ξω.2⟩

end StatMech.FrontierD
