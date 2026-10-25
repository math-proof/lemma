/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz


namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


theorem hexBrickPos_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexBrickPos (hexAWNeighbor c e) =
      hexBrickPos c + stepOf (hexBrickDir (hexAWHeadingMod c e)) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexBrickPos, hexAWNeighbor, hexAWHeadingMod, hexBrickDir, stepOf,
      Prod.ext_iff] <;> omega


theorem hexBrickPos_injective : Function.Injective hexBrickPos := by
  intro c d h
  rcases c with ⟨i, j, color⟩
  rcases d with ⟨i', j', color'⟩
  cases color <;> cases color' <;>
    simp [hexBrickPos, Prod.ext_iff] at h ⊢ <;> omega


end StatMech.Universality
