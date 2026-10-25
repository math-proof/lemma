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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part14


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_eisenstein_horizontal (d : HexReturnCoord) :
    (2 * (d.value * halfStep 0)).re =
      (Real.sqrt 3 / 2) * (d.x - d.y) := by
  rw [show d.value * halfStep 0 =
      (d.x : ℂ) * halfStep 0 + (d.y : ℂ) * (hexOmega * halfStep 0) by
    simp [HexReturnCoord.value]
    ring]
  rw [← hexConcrete_halfStep_add2 0]
  norm_num [Complex.mul_re, Complex.add_re,
    hlhr_halfStep_zero_re, hlhr_halfStep_two_re]
  ring


theorem hlhr_height_eq_latticeHeight (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (k : ℕ) :
    hlhr_height 0 ts k = Real.sqrt 3 / 4 +
      (Real.sqrt 3 / 2) * hlhr_latticeHeight ts k := by
  have htake : ∀ t ∈ ts.take k, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)
  have hbase : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have hgeom := (hlhr_coordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base 0 (halfStep 0) 0 (ts.take k) hbase htake).1
  have hlast := hexInfra_ofTurns_last_re (0 : ℂ) 0 (ts.take k)
  rw [hgeom] at hlast
  rw [hlhr_height, hexW2_partialDisp]
  have hlast' : hexInfra_stepReSum 0 (ts.take k) +
      (halfStep (hexInfra_headAccum 0 (ts.take k))).re =
      (0 + halfStep 0 +
        2 * (((hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
          (ts.take k)).pos.value - HexReturnCoord.zero.value) * halfStep 0)).re := by
    simpa using hlast.symm
  rw [hlast']
  simp only [HexReturnCoord.value_zero, sub_zero, Complex.add_re,
    zero_add]
  rw [hlhr_halfStep_zero_re,
    hlhr_eisenstein_horizontal]
  simp [hlhr_latticeHeight]


end StatMech.Universality
