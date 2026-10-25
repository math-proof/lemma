/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part7
import Def.StatisticalMechanics.Code.Universality.HexStripWindingClose.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexUmlauf_band_singleRight_bound (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
    (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
    |hexInfra_headAccum h0 [(-1 : ℤ)]
        - (hexUmlauf_band_singleRight a h0 inReg hclass).H| < 6 :=
  hexUmlauf_bound_of_band inReg a h0
    (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)))
    (hexUmlauf_band_singleRight a h0 inReg hclass) [(-1 : ℤ)]
    ⟨hexW1Exit_singleRight_legal a h0, hstay, hexW1Exit_singleRight_endsAt a h0⟩


theorem hexUmlauf_no_full_revolution (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (B : HexStripBand inRegion a h0 z) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (k : ℕ) (hk : k ≤ ts.length) :
    hexStripWinding_runningHead h0 ts k < B.w + 6 :=
  (B.windowField ts hadm k hk).2

end StatMech.Universality
