/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part8


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_normalizeCoord_depth (up : Bool) (source c : HexAWCoord) :
    hexAWDepth (hlhd_normalizeCoord up source c) =
      if up then hexAWDepth c - hexAWDepth source
      else hexAWDepth source - hexAWDepth c := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> simp [hlhd_normalizeCoord, hexAWDepth, hexAWLong] <;> omega

theorem hlhd_normalizeCoord_neighbor (up : Bool) (source c : HexAWCoord)
    (e : Fin 3) :
    hlhd_normalizeCoord up source (hexAWNeighbor c e) =
      hexAWNeighbor (hlhd_normalizeCoord up source c) e := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> cases color <;> fin_cases e <;>
    simp [hlhd_normalizeCoord, hlhd_swapColor, hexAWNeighbor] <;> omega

theorem hlhd_normalizeCoord_source_up (source : HexAWCoord)
    (hc : source.color = .black) :
    hlhd_normalizeCoord true source source = hexAWOriginCoord := by
  rcases source with ⟨i, j, color⟩
  cases color <;> simp_all [hlhd_normalizeCoord, hlhd_swapColor,
    hexAWOriginCoord]

theorem hlhd_normalizeCoord_source_down (source : HexAWCoord)
    (hc : source.color = .white) :
    hlhd_normalizeCoord false source source = hexAWOriginCoord := by
  rcases source with ⟨i, j, color⟩
  cases color <;> simp_all [hlhd_normalizeCoord, hlhd_swapColor,
    hexAWOriginCoord]

theorem hlhd_normalizeCoord_heading (up : Bool) (source c : HexAWCoord)
    (e : Fin 3) :
    hexAWHeading (hlhd_normalizeCoord up source c) e =
      if up then hexAWHeading c e
      else match c.color with
        | .black => hexAWHeading c e + 3
        | .white => hexAWHeading c e - 3 := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> cases color <;> fin_cases e <;>
    simp [hlhd_normalizeCoord, hlhd_swapColor, hexAWHeading]

theorem hlhd_normalizeCoord_pos (up : Bool) (source c : HexAWCoord)
    (hsource : if up then source.color = .black else source.color = .white) :
    hexAWPos (hlhd_normalizeCoord up source c) =
      if up then hexAWPos c - hexAWPos source
      else hexAWPos source - hexAWPos c := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> cases sc <;> cases color <;>
    simp_all [hlhd_normalizeCoord, hlhd_swapColor, hexAWPos] <;> ring


end
end StatMech.Universality
