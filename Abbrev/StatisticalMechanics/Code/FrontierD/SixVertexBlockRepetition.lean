/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition
open Finset


namespace StatMech.FrontierD

abbrev SixVertexRectangleBlockCopies {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) (a b : ℕ) :=
  Fin (a + 1) × Fin (b + 1) →
    SixVertexRectangleBoundaryFiber (sixVertexToroidalRectangleBoundary ξ)


end StatMech.FrontierD
