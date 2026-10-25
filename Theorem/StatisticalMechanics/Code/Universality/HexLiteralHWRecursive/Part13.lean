/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part13


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_coordRun_geometry (p d : HexReturnCoord) (m s : ℂ)
    (h : ℤ) (ts : List ℤ)
    (hdir : halfStep h = d.value * s)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    let r := hlhr_coordRun p d ts
    hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) =
        m + halfStep h + 2 * ((r.pos.value - p.value) * s) ∧
      halfStep (hexInfra_headAccum h ts) = r.dir.value * s := by
  induction ts generalizing p d m h with
  | nil =>
      constructor
      · simp [hlhr_coordRun]
      · simpa [hlhr_coordRun] using hdir
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : halfStep (h + t) = e.value * s :=
        hexReturn_halfStep_turn s h d t hdir ht
      have hrec := ih (p.add e) e
        (m + halfStep h + halfStep (h + t)) (h + t) he htail
      simp only [hlhr_coordRun, hexInfra_midAccum_cons,
        hexInfra_headAccum_cons]
      simp only [HexReturnCoord.value_add] at hrec
      constructor
      · rw [hrec.1, he]
        ring
      · exact hrec.2


theorem hlhr_halfStep_zero_re : (halfStep 0).re = Real.sqrt 3 / 4 := by
  rw [hexWall3_halfStep_re]
  rw [show Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 by norm_num,
    Real.cos_pi_div_six]
  ring


theorem hlhr_halfStep_two_re : (halfStep 2).re = -(Real.sqrt 3 / 4) := by
  rw [hexWall3_halfStep_re]
  rw [show Real.pi / 6 + ((2 : ℤ) : ℝ) * (Real.pi / 3) = 5 * Real.pi / 6 by
      push_cast; ring,
    show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_six]
  ring


end StatMech.Universality
