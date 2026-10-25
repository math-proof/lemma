/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Def.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

@[simp] theorem hexAWLowerSlantWitnessCoord_mem (L : ℕ) :
    hexAWLowerSlantWitnessCoord L ∈ hexAWVertexSet 2 L := by
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWLowerSlantWitnessCoord, hexAWInStrip, hexAWBookRe2,
    hexAWBookSqrt3Im2, hexAWDepth, hexAWLong, hexAWTrans]
  omega

@[simp] theorem hexAWUpperSlantWitnessCoord_mem (L : ℕ) :
    hexAWUpperSlantWitnessCoord L ∈ hexAWVertexSet 2 L := by
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWUpperSlantWitnessCoord, hexAWInStrip, hexAWBookRe2,
    hexAWBookSqrt3Im2, hexAWDepth, hexAWLong, hexAWTrans]
  omega


end
end StatMech.Universality
