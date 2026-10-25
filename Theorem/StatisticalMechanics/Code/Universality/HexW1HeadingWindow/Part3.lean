/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Def.StatisticalMechanics.Code.Universality.HexW1HeadingWindow


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


namespace HexWindingBound

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (S : HexWindingBound inRegion a h0 z)


@[simp] theorem toBoundarySide_H : S.toBoundarySide.H = S.H := rfl

@[simp] theorem toBoundarySide_w : S.toBoundarySide.w = S.w := rfl


theorem turning_const (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
    (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((S.H : ℝ) - (h0 : ℝ)) :=
  S.toBoundarySide.turning_const ts hadm

end HexWindingBound


theorem hexW1_windingSidePhaseLock (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (zt zb : ℂ)
    (σ x W r : ℝ)
    (Bt : HexWindingBound inRegion a h0 zt) (Bb : HexWindingBound inRegion a h0 zb)
    (hWt : (Real.pi / 3) * ((Bt.H : ℝ) - (h0 : ℝ)) = W)
    (hWb : (Real.pi / 3) * ((Bb.H : ℝ) - (h0 : ℝ)) = -W)
    (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
    (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
    parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x
      = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) :=
  hexW1_sidePhaseLock inRegion a h0 zt zb σ x W r Bt.toBoundarySide Bb.toBoundarySide
    hWt hWb hreflt hreflb


end StatMech.Universality
