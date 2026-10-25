/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Def.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


@[simp] theorem hexInfra_stepReSum_nil (h : ℤ) : hexInfra_stepReSum h [] = 0 := rfl

@[simp] theorem hexInfra_stepReSum_cons (h t : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h (t :: ts)
      = (HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re + hexInfra_stepReSum (h + t) ts :=
  rfl


theorem hexInfra_midAccum_re (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum m h ts).re = m.re + hexInfra_stepReSum h ts := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih =>
    rw [hexInfra_midAccum_cons, ih, hexInfra_stepReSum_cons]
    simp only [Complex.add_re]
    ring


theorem hexInfra_ofTurns_last_re (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)).re
      = a.re + hexInfra_stepReSum h0 ts + (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re := by
  rw [Complex.add_re, hexInfra_midAccum_re]


theorem hexInfra_halfStep_re_abs_le (h : ℤ) : |(HexWalk.halfStep h).re| ≤ 1 / 2 := by
  have hre : (HexWalk.halfStep h).re
      = (1 / 2) * Real.cos (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
    unfold HexWalk.halfStep hexUnit
    rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((h : ℝ)) : ℂ) * ((Real.pi : ℂ) / 3)))
          = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
    norm_num
  rw [hre, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith [Real.abs_cos_le_one (Real.pi / 6 + (h : ℝ) * (Real.pi / 3))]


theorem hexInfra_halfStep_re_le (h : ℤ) : (HexWalk.halfStep h).re ≤ 1 / 2 :=
  (abs_le.mp (hexInfra_halfStep_re_abs_le h)).2


theorem hexInfra_stepReSum_le_length (h : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h ts ≤ ts.length := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih =>
    rw [hexInfra_stepReSum_cons, List.length_cons]
    have h1 := hexInfra_halfStep_re_le h
    have h2 := hexInfra_halfStep_re_le (h + t)
    have hih := ih (h + t)
    push_cast
    linarith


theorem hexInfra_verticesAux_last_re_le (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)).re
      ≤ m.re + (ts.length + 1) := by
  rw [Complex.add_re, hexInfra_midAccum_re]
  have h1 := hexInfra_stepReSum_le_length h ts
  have h2 := hexInfra_halfStep_re_le (hexInfra_headAccum h ts)
  linarith


end StatMech.Universality
