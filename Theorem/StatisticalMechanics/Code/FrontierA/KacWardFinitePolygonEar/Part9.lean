/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part8


namespace StatMech.FrontierA

theorem kwAngleTurnNoWrap_or_wrap (a b c : Real.Angle)
    (hab : b - a ≠ (Real.pi : Real.Angle))
    (hbc : c - b ≠ (Real.pi : Real.Angle))
    (hac : c - a ≠ (Real.pi : Real.Angle)) :
    kwAngleTurnNoWrap a b c ∨ kwAngleTurnWrap a b c := by
  by_cases hsame : (b - a).sign = (c - b).sign
  · by_cases houter : (b - a).sign = (c - a).sign
    · exact Or.inl ⟨hab, hbc, Or.inr houter⟩
    · exact Or.inr ⟨hab, hbc, hac, hsame, houter⟩
  · exact Or.inl ⟨hab, hbc, Or.inl hsame⟩


end StatMech.FrontierA
