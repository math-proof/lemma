module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part4
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable instance sixVertexToroidalBoundaryBalancedDecidable {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) : Decidable ξ.Balanced :=
  Classical.propDecidable _


end StatMech.FrontierD
