/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part7
import Def.StatisticalMechanics.Code.Universality.HexStripWindingClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


@[simp] theorem hexUmlauf_stripWinding_of_band_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) :
    (hexUmlauf_stripWinding_of_band inRegion a h0 z B).H = B.H := rfl

@[simp] theorem hexUmlauf_stripWinding_of_band_w (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) :
    (hexUmlauf_stripWinding_of_band inRegion a h0 z B).w = B.w := rfl


theorem hexUmlauf_bound_of_band (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    |hexInfra_headAccum h0 ts - B.H| < 6 :=
  (hexUmlauf_stripWinding_of_band inRegion a h0 z B).bound ts hadm


end StatMech.Universality
