/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Structure.StatisticalMechanics.Code.Universality.HexContourDefs


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


noncomputable def hexContourLambda (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (sides : HexContourSides) (x : ℝ) : ℝ :=
  hexContourSum inRegion a h0 sides.bottom x


noncomputable def hexContourTauPlus (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (sides : HexContourSides) (x : ℝ) : ℝ :=
  hexContourSum inRegion a h0 sides.slantPlus x


noncomputable def hexContourTauMinus (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (sides : HexContourSides) (x : ℝ) : ℝ :=
  hexContourSum inRegion a h0 sides.slantMinus x


noncomputable def hexContourUpsilon (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (sides : HexContourSides) (x : ℝ) : ℝ :=
  hexContourSum inRegion a h0 sides.top x

end StatMech.Universality
