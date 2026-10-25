/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part2
open Finset


namespace StatMech.FrontierD

noncomputable def sixVertexRectangleBoundaryPartitionSum
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) : ℝ :=
  ∑ ω : SixVertexRectangleArrows N M,
    if sixVertexRectangleBoundary ω = ξ then ω.weight c else 0


noncomputable def sixVertexRectangleFreePartitionSum (N M : ℕ) (c : ℝ) : ℝ :=
  ∑ ω : SixVertexRectangleArrows N M, ω.weight c


noncomputable def sixVertexRectangleToroidalPartitionSum (N M : ℕ) (c : ℝ) : ℝ :=
  ∑ ξ : SixVertexToroidalBoundary N M,
    sixVertexRectangleBoundaryPartitionSum N M c
      (sixVertexToroidalRectangleBoundary ξ)


noncomputable def sixVertexRectangleBalancedPartitionSum (N M : ℕ) (c : ℝ) : ℝ :=
  ∑ ξ : SixVertexToroidalBoundary N M,
    if ξ.Balanced then
      sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ)
    else 0

end StatMech.FrontierD
