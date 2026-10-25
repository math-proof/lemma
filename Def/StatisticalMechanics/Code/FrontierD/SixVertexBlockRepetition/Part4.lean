/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part4
open Finset


namespace StatMech.FrontierD

noncomputable def sixVertexRectangleMaxBalancedBoundaryContribution
    (N M : ℕ) (c : ℝ) : ℝ :=
  (Finset.univ.image fun ξ : SixVertexToroidalBoundary N M =>
    if ξ.Balanced then
      sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ)
    else 0).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

end StatMech.FrontierD
