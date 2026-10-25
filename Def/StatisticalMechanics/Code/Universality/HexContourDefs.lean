/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


def hexContourFamily (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (side : Set ℂ) :
    Set (List ℤ) :=
  {ts | (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧
    ∃ z ∈ side, (ofTurns a h0 ts).EndsAt z}


noncomputable def hexContourSum (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (side : Set ℂ) (x : ℝ) : ℝ :=
  ∑' ts : {ts // ts ∈ hexContourFamily inRegion a h0 side},
    x ^ (ofTurns a h0 ts.1).numVertices


end StatMech.Universality
