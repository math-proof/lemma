/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricCovering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricAnalytic.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricCovering
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexOddPositiveHalfProjection (m : Nat) :
    (Fin ((m + 1) + m) → Real) →L[Real] (Fin m → Real) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (sixVertexOddPositiveIndex m j)

end
end StatMech.FrontierD
