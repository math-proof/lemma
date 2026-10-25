/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part9
open Finset


namespace StatMech.FrontierD

abbrev SixVertexRectangleBalancedBoundaryFibers (N M : ℕ) :=
  Σ ξ : {ξ : SixVertexToroidalBoundary N M // ξ.Balanced},
    SixVertexRectangleBoundaryFiber
      (sixVertexToroidalRectangleBoundary ξ.1)


end StatMech.FrontierD
