/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Universality.HexVertex


namespace StatMech.Universality

open Complex


namespace VertexWalkData

variable (D : VertexWalkData)


noncomputable def vertexSum : ℂ :=
  (∑ P ∈ D.pairs,
      (hexContribution (hexOmega * D.du) (D.pairWind P - 4) (D.pairLen P)
        + hexContribution (hexOmega ^ 2 * D.du) (D.pairWind P + 4) (D.pairLen P)))
  + (∑ T ∈ D.triplets,
      (hexContribution D.du (D.tripWind T) (D.tripLen T)
        + hexContribution (hexOmega * D.du) (D.tripWind T - 1) (D.tripLen T + 1)
        + hexContribution (hexOmega ^ 2 * D.du) (D.tripWind T + 1) (D.tripLen T + 1)))


end VertexWalkData
end StatMech.Universality
