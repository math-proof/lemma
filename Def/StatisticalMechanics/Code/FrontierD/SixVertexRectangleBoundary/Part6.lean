/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part2
open Finset


namespace StatMech.FrontierD

noncomputable def sixVertexRectangleMaxToroidalBoundaryPartitionSum
    (N M : ℕ) (c : ℝ) : ℝ :=
  (Finset.univ.image fun ξ : SixVertexToroidalBoundary N M =>
    sixVertexRectangleBoundaryPartitionSum N M c
      (sixVertexToroidalRectangleBoundary ξ)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

end StatMech.FrontierD
