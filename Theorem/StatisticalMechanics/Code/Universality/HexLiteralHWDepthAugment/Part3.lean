/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_firstDir_mem_edgeVertices (d : HexReturnCoord) (ts : List ℤ) :
    d ∈ hlha_edgeVertices HexReturnCoord.zero d ts := by
  cases ts with
  | nil => simp [hlha_edgeVertices, hlha_zero_add]
  | cons t ts =>
      simp only [hlha_edgeVertices, List.mem_cons]
      right
      simpa [hlha_zero_add] using
        hlha_edgeVertices_start_mem d (d.turn t) ts

theorem hlhda_halfSpace_congr {xs ys : List ℤ} (hxy : xs = ys)
    {hx : (ofTurns hexAWStart 1 xs).IsLegalSAW}
    {hy : (ofTurns hexAWStart 1 ys).IsLegalSAW}
    (hhalf : HLHDLiteralHalfSpace xs hx) :
    HLHDLiteralHalfSpace ys hy := by
  subst ys
  have hp : hx = hy := Subsingleton.elim _ _
  subst hy
  exact hhalf

end
end StatMech.Universality
