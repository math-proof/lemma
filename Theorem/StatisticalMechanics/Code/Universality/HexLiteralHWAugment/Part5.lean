/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part5


namespace StatMech.Universality

open HexWalk


theorem hlha_standard_vertices (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) :
    (ofTurns 0 0 ts).vertices =
      (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).map
        hlha_standardRealize := by
  have hdir : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have h := hlha_verticesAux_coord HexReturnCoord.zero HexReturnCoord.base
    0 (halfStep 0) 0 ts hdir hlegal
  change verticesAux 0 0 ts = _
  rw [h]
  apply List.map_congr_left
  intro p _
  simp [hlha_realizeCoord, hlha_standardRealize,
    HexReturnCoord.value_zero]

theorem hlha_value_injective :
    Function.Injective HexReturnCoord.value := by
  intro p q h
  have hz : (((p.x - q.x : ℤ) : ℝ) : ℂ) +
      (((p.y - q.y : ℤ) : ℝ) : ℂ) * hexOmega = 0 := by
    unfold HexReturnCoord.value at h
    push_cast
    linear_combination h
  obtain ⟨hx, hy⟩ := hexConcrete_omega_lin_indep
    ((p.x - q.x : ℤ) : ℝ) ((p.y - q.y : ℤ) : ℝ) hz
  have hx0 : p.x - q.x = 0 := by exact_mod_cast hx
  have hy0 : p.y - q.y = 0 := by exact_mod_cast hy
  have hx' : p.x = q.x := sub_eq_zero.mp hx0
  have hy' : p.y = q.y := sub_eq_zero.mp hy0
  cases p
  cases q
  simp_all

theorem hlha_standardRealize_injective :
    Function.Injective hlha_standardRealize := by
  intro p q h
  apply hlha_value_injective
  have hstep : halfStep 0 ≠ 0 := hexConcrete_halfStep_ne 0
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  unfold hlha_standardRealize at h
  have hm : (p.value - q.value) * halfStep 0 = 0 := by
    apply (mul_left_cancel₀ htwo)
    linear_combination h
  rcases mul_eq_zero.mp hm with hpq | hs
  · exact sub_eq_zero.mp hpq
  · exact (hstep hs).elim


theorem hlha_standard_isSAW_iff (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) :
    (ofTurns 0 0 ts).IsSAW ↔
      (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).Nodup := by
  rw [IsSAW, hlha_standard_vertices ts hlegal,
    List.nodup_map_iff hlha_standardRealize_injective]


theorem hlha_coordRun_take_mem_tail (p d : HexReturnCoord) (ts : List ℤ)
    {k : ℕ} (hk : 0 < k) (hkle : k ≤ ts.length) :
    (hlhr_coordRun p d (ts.take k)).pos ∈
      (hlha_coordVertices p d ts).tail := by
  induction ts generalizing p d k with
  | nil =>
      simp only [List.length_nil] at hkle
      omega
  | cons t ts ih =>
      cases k with
      | zero => omega
      | succ j =>
          simp only [List.take_succ_cons, hlhr_coordRun,
            hlha_coordVertices, List.tail_cons]
          cases j with
          | zero =>
              have hstart : p.add (d.turn t) ∈
                  hlha_coordVertices (p.add (d.turn t)) (d.turn t) ts := by
                cases ts <;> simp [hlha_coordVertices]
              simpa [hlhr_coordRun] using hstart
          | succ j =>
              apply List.mem_of_mem_tail
              exact ih (p.add (d.turn t)) (d.turn t) (k := j + 1)
                (by omega) (by
                  simp only [List.length_cons] at hkle
                  omega)


theorem hlha_augmentSide_latticeHeight_pos (d : HexReturnCoord)
    (ts : List ℤ) (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts,
      p.x - p.y ≤ 0) {k : ℕ} (hk : 0 < k)
    (hkle : k ≤ (hlha_augmentSide d ts).length) :
    0 < hlhr_latticeHeight (hlha_augmentSide d ts) k := by
  have hmem := hlha_coordRun_take_mem_tail HexReturnCoord.zero
    HexReturnCoord.base (hlha_augmentSide d ts) hk hkle
  rw [hlha_coordVertices_augmentSide d ts hd hlegal] at hmem
  simp only [List.tail_cons, List.mem_map] at hmem
  obtain ⟨p, hp, heq⟩ := hmem
  have hpos := hlha_augmented_vertex_height_pos d p (hbehind p hp)
  unfold hlhr_latticeHeight
  change 0 <
    (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
      ((hlha_augmentSide d ts).take k)).pos.x -
    (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
      ((hlha_augmentSide d ts).take k)).pos.y
  rw [← heq]
  exact hpos


theorem hlha_augmentSide_halfSpace (d : HexReturnCoord)
    (ts : List ℤ) (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts,
      p.x - p.y ≤ 0) :
    HLHRLiteralHalfSpace 0 (hlha_augmentSide d ts) := by
  intro k hk hkle
  have hturns : (ofTurns 0 0 (hlha_augmentSide d ts)).LegalTurns :=
    hlha_augmentSide_legal d ts hlegal
  rw [hlhr_height_eq_latticeHeight _ hturns 0,
    hlhr_height_eq_latticeHeight _ hturns k]
  have hkpos := hlha_augmentSide_latticeHeight_pos d ts hd hlegal
    hbehind hk hkle
  have hzero : hlhr_latticeHeight (hlha_augmentSide d ts) 0 = 0 := rfl
  rw [hzero]
  norm_num
  exact hkpos


theorem hlha_augmentSide_isLegalSAW (d : HexReturnCoord)
    (ts : List ℤ) (hd : HLHAAwayDir d)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hnodup : (hlha_edgeVertices HexReturnCoord.zero d ts).Nodup)
    (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts,
      p.x - p.y ≤ 0) :
    (ofTurns 0 0 (hlha_augmentSide d ts)).IsLegalSAW := by
  have hturns : (ofTurns 0 0 (hlha_augmentSide d ts)).LegalTurns :=
    hlha_augmentSide_legal d ts hlegal
  refine ⟨hturns, ?_⟩
  rw [hlha_standard_isSAW_iff _ hturns]
  exact hlha_coordVertices_augmentSide_nodup d ts hd hlegal hnodup hbehind


theorem hlha_coordRun_direction_isUnit (p d : HexReturnCoord)
    (ts : List ℤ) (hd : d.IsUnit)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hlhr_coordRun p d ts).dir.IsUnit := by
  induction ts generalizing p d with
  | nil => simpa [hlhr_coordRun] using hd
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simpa [hlhr_coordRun] using
        ih (p.add (d.turn t)) (d.turn t) (d.isUnit_turn hd ht) htail


theorem hlha_mem_coordVertices (p d : HexReturnCoord) (ts : List ℤ)
    {q : HexReturnCoord} (hq : q ∈ hlha_coordVertices p d ts) :
    ∃ k, k ≤ ts.length ∧ q = (hlhr_coordRun p d (ts.take k)).pos := by
  induction ts generalizing p d q with
  | nil =>
      simp [hlha_coordVertices] at hq
      subst q
      exact ⟨0, by simp, by simp [hlhr_coordRun]⟩
  | cons t ts ih =>
      simp only [hlha_coordVertices, List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        exact ⟨0, by simp, by simp [hlhr_coordRun]⟩
      · obtain ⟨k, hk, heq⟩ :=
          ih (p.add (d.turn t)) (d.turn t) (q := q) hq
        refine ⟨k + 1, by simp; omega, ?_⟩
        simp only [List.take_succ_cons, hlhr_coordRun]
        exact heq


theorem hlha_coordVertices_drop (p d : HexReturnCoord) (ts : List ℤ)
    (cp : ℕ) (hcp : cp ≤ ts.length) :
    let r := hlhr_coordRun p d (ts.take cp)
    hlha_coordVertices r.pos r.dir (ts.drop cp) =
      (hlha_coordVertices p d ts).drop cp := by
  induction ts generalizing p d cp with
  | nil =>
      have : cp = 0 := by simpa using hcp
      subst cp
      simp [hlhr_coordRun, hlha_coordVertices]
  | cons t ts ih =>
      cases cp with
      | zero => simp [hlhr_coordRun, hlha_coordVertices]
      | succ cp =>
          simp only [List.take_succ_cons, List.drop_succ_cons, hlhr_coordRun,
            hlha_coordVertices, List.drop_succ_cons]
          apply ih
          simp only [List.length_cons] at hcp
          omega


theorem hlha_cut_latticeHeight_max (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (k : ℕ)
    (hk : k ≤ ts.length) :
    hlhr_latticeHeight ts k ≤
      hlhr_latticeHeight ts (hexW2_cutPos 0 ts) := by
  have hmax := hexW2_cutPos_max 0 ts k hk
  change hlhr_height 0 ts k ≤
    hlhr_height 0 ts (hexW2_cutPos 0 ts) at hmax
  rw [hlhr_height_eq_latticeHeight ts hlegal k,
    hlhr_height_eq_latticeHeight ts hlegal (hexW2_cutPos 0 ts)] at hmax
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  have hcast : (hlhr_latticeHeight ts k : ℝ) ≤
      (hlhr_latticeHeight ts (hexW2_cutPos 0 ts) : ℝ) := by
    nlinarith
  exact_mod_cast hcast


theorem hlha_source_standard_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns 0 0 ts).IsLegalSAW :=
  (hhe_isLegalSAW_rebase a 0 h0 0 ts).mpr hlegal


theorem hlha_source_coord_nodup (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
    (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).Nodup := by
  have hs := hlha_source_standard_legal a h0 ts hlegal
  exact (hlha_standard_isSAW_iff ts hs.1).mp hs.2


theorem hlha_awayDir_of_isUnit_of_height_nonpos (d : HexReturnCoord)
    (hu : d.IsUnit) (hh : d.x - d.y ≤ 0) : HLHAAwayDir d := by
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HLHAAwayDir] at hh ⊢


end StatMech.Universality
