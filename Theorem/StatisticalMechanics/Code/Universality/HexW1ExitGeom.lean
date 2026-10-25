/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexW1Exit_halfStep_add_three (h : ℤ) :
    HexWalk.halfStep (h + 3) = - HexWalk.halfStep h := by
  unfold HexWalk.halfStep
  rw [hexUnit_add_three]; ring


theorem hexW1Exit_penult_mem (m : ℂ) (h : ℤ) (t : ℤ) (ts : List ℤ) :
    hexInfra_midAccum m h (t :: ts) - HexWalk.halfStep (hexInfra_headAccum h (t :: ts))
      ∈ HexWalk.verticesAux m h (t :: ts) := by
  induction ts generalizing m h t with
  | nil =>
    rw [hexInfra_midAccum_cons, hexInfra_midAccum_nil, hexInfra_headAccum_cons,
      hexInfra_headAccum_nil, HexWalk.verticesAux_cons]
    have : m + HexWalk.halfStep h + HexWalk.halfStep (h + t) - HexWalk.halfStep (h + t)
        = m + HexWalk.halfStep h := by ring
    rw [this]
    exact List.mem_cons_self
  | cons s ss ih =>
    rw [HexWalk.verticesAux_cons]
    refine List.mem_cons_of_mem _ ?_
    have key : hexInfra_midAccum m h (t :: s :: ss)
          - HexWalk.halfStep (hexInfra_headAccum h (t :: s :: ss))
        = hexInfra_midAccum (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) (s :: ss)
          - HexWalk.halfStep (hexInfra_headAccum (h + t) (s :: ss)) := by
      rw [hexInfra_midAccum_cons, hexInfra_headAccum_cons]
    rw [key]
    exact ih (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) s


theorem hexW1Exit_halfStep_ne_zero (h : ℤ) : HexWalk.halfStep h ≠ 0 := by
  unfold HexWalk.halfStep
  exact mul_ne_zero (by norm_num) (hexUnit_ne_zero h)


theorem hexW1Exit_penult_eq_of_endsAt (a : ℂ) (h0 : ℤ) (z : ℂ) (t : ℤ) (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
    z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      ∈ (HexWalk.ofTurns a h0 (t :: ts)).vertices := by
  have hzm : hexInfra_midAccum a h0 (t :: ts) = z := by
    rw [← hexInfra_endMid_eq_midAccum]; exact hz
  rw [← hzm]
  exact hexW1Exit_penult_mem a h0 t ts


theorem hexW1Exit_penult_ne_last (z : ℂ) (H : ℤ) :
    z - HexWalk.halfStep H ≠ z + HexWalk.halfStep H := by
  intro hc
  have : HexWalk.halfStep H + HexWalk.halfStep H = 0 := by linear_combination -hc
  have h2 : (2 : ℂ) * HexWalk.halfStep H = 0 := by linear_combination this
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact hexW1Exit_halfStep_ne_zero H h


theorem hexW1Exit_lastVertex_eq_iff (a : ℂ) (h0 : ℤ) (z : ℂ) (H : ℤ) (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 ts).EndsAt z) :
    (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
        = z + HexWalk.halfStep H)
      ↔ HexWalk.halfStep (hexInfra_headAccum h0 ts) = HexWalk.halfStep H := by
  have hzm : hexInfra_midAccum a h0 ts = z := by
    rw [← hexInfra_endMid_eq_midAccum]; exact hz
  rw [hzm]
  constructor
  · intro h; exact add_left_cancel h
  · intro h; rw [h]


theorem hexW1Exit_lastVertex_of_dir (a : ℂ) (h0 : ℤ) (z : ℂ) (H : ℤ) (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
    (hdir : HexWalk.halfStep (hexInfra_headAccum h0 ts) = HexWalk.halfStep H) :
    hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
      = z + HexWalk.halfStep H :=
  (hexW1Exit_lastVertex_eq_iff a h0 z H ts hz).mpr hdir


end StatMech.Universality
