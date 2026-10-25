/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalDensityPerronPositiveHalfRoots
    {c : Real} (hc : 2 < c) (k : Nat) : Fin (k + 1) → Real :=
  sixVertexEvenPositiveHalfProjection (k + 1)
    (sixVertexCanonicalDensityPerronBetheRoots hc k)

def sixVertexCanonicalDensityPerronPositiveHalfRootFamily
    {c : Real} (hc : 2 < c) : SixVertexSymmetricHalfFilledRoots :=
  fun k => sixVertexCanonicalDensityPerronPositiveHalfRoots hc k

end
end StatMech.FrontierD
