/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hcm_vertex_is_prefix_last (a : ℂ) (h0 : ℤ) (ts : List ℤ) (v : ℂ)
    (hv : v ∈ verticesAux a h0 ts) :
    ∃ k ≤ ts.length, v = hexInfra_midAccum a h0 (ts.take k)
      + HexWalk.halfStep (hexInfra_headAccum h0 (ts.take k)) := by
  induction ts generalizing a h0 with
  | nil =>
    rw [verticesAux_nil, List.mem_singleton] at hv
    exact ⟨0, by simp, by simp [hv]⟩
  | cons t ts ih =>
    rw [verticesAux_cons, List.mem_cons] at hv
    rcases hv with h | h
    · exact ⟨0, by simp, by simp [h]⟩
    · obtain ⟨k, hk, hkv⟩ := ih (a + halfStep h0 + halfStep (h0 + t)) (h0 + t) h
      refine ⟨k + 1, by simp; omega, ?_⟩
      rw [List.take_succ_cons, hexInfra_midAccum_cons, hexInfra_headAccum_cons]
      exact hkv


theorem hcm_vertex_re_le_cutDisp (a : ℂ) (h0 : ℤ) (ts : List ℤ) (v : ℂ)
    (hv : v ∈ verticesAux a h0 ts) :
    v.re ≤ a.re + hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) := by
  obtain ⟨k, hk, hkv⟩ := hcm_vertex_is_prefix_last a h0 ts v hv
  rw [hkv, hexInfra_ofTurns_last_re a h0 (ts.take k)]
  have hmax := hexW2_cutPos_max h0 ts k hk
  unfold hexW2_partialDisp at hmax ⊢
  linarith


theorem hcm_stMid_eq_midAccum (m : ℂ) (h : ℤ) (ts : List ℤ) :
    hfs_stMid m h ts = hexInfra_midAccum m h ts := by
  induction ts generalizing m h with
  | nil => simp [hfs_stMid, hexInfra_midAccum]
  | cons t ts ih => simp [hfs_stMid, hexInfra_midAccum, ih]


theorem hcm_stHead_eq_headAccum (h : ℤ) (ts : List ℤ) :
    hfs_stHead h ts = hexInfra_headAccum h ts := by
  induction ts generalizing h with
  | nil => simp [hfs_stHead, hexInfra_headAccum]
  | cons t ts ih => simp [hfs_stHead, hexInfra_headAccum, ih]


theorem hcm_first_vertex_mem (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    a + halfStep h0 ∈ verticesAux a h0 ts := by
  cases ts with
  | nil => rw [verticesAux_nil]; exact List.mem_singleton.mpr rfl
  | cons x xs => rw [verticesAux_cons]; exact List.mem_cons_self


theorem hcm_dropStart_re (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ) :
    (hfs_stMid a h0 (ts.take cp)).re
      + (HexWalk.halfStep (hfs_stHead h0 (ts.take cp))).re
      = a.re + hexW2_partialDisp h0 ts cp := by
  rw [hcm_stMid_eq_midAccum, hcm_stHead_eq_headAccum, hexInfra_midAccum_re]
  unfold hexW2_partialDisp
  ring


end StatMech.Universality
