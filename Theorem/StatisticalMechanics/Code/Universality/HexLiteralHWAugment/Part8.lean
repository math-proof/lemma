/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part8


namespace StatMech.Universality

open HexWalk


theorem hlha_negCoord_isUnit {d : HexReturnCoord} (hd : d.IsUnit) :
    (hlha_negCoord d).IsUnit := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HexReturnCoord.IsUnit, hlha_negCoord]

theorem hlha_coordVertices_take (p d : HexReturnCoord) (ts : List ℤ)
    (cp : ℕ) :
    hlha_coordVertices p d (ts.take cp) =
      (hlha_coordVertices p d ts).take (cp + 1) := by
  induction ts generalizing p d cp with
  | nil =>
      cases cp <;> simp [hlha_coordVertices]
  | cons t ts ih =>
      cases cp with
      | zero => simp [hlha_coordVertices]
      | succ cp =>
          rw [List.take_succ_cons, hlha_coordVertices, hlha_coordVertices,
            List.take_succ_cons, ih]

theorem hlha_prefix_side_hypotheses (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (hsource : (ofTurns a h0 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hprefix : ts.take (hexW2_cutPos 0 ts) = t :: us) :
    let d := hlha_negCoord (hlha_cutState ts).dir
    HLHAAwayDir d ∧
      (∀ u ∈ loopReverse us, u = 1 ∨ u = -1) ∧
      (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).Nodup ∧
      ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d (loopReverse us),
        p.x - p.y ≤ 0 := by
  have hstd := hlha_source_standard_legal a h0 ts hsource
  have hcple := hexW2_cutPos_le 0 ts
  let r := hlha_cutState ts
  let d0 := HexReturnCoord.base.turn t
  let d := hlha_negCoord r.dir
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_take
    rw [hprefix]
    simp
  have ht := hstd.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hutake : u ∈ ts.take (hexW2_cutPos 0 ts) := by
      rw [hprefix]
      simp [hu]
    exact hstd.1 u (List.mem_of_mem_take hutake)
  have hrevlegal : ∀ u ∈ loopReverse us, u = 1 ∨ u = -1 :=
    loopReverse_legal us hus
  have hrstate : hlhr_coordRun (HexReturnCoord.zero.add d0) d0 us = r := by
    dsimp [r, hlha_cutState, d0]
    rw [hprefix]
    simp only [hlhr_coordRun]
  have hrev := hlha_edgeVertices_loopReverse HexReturnCoord.zero d0 us hus
  rw [hrstate] at hrev
  have hprefixCoords :
      hlha_edgeVertices HexReturnCoord.zero d0 us =
        (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).take
          (hexW2_cutPos 0 ts + 1) := by
    rw [← hlha_coordVertices_take]
    rw [hprefix, hlha_coordVertices_cons_eq_edge]
  have habs :
      hlha_edgeVertices r.pos d (loopReverse us) =
        ((hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).take
          (hexW2_cutPos 0 ts + 1)).reverse := by
    dsimp [d]
    rw [hrev.1, hprefixCoords]
  have htrans :
      hlha_edgeVertices r.pos d (loopReverse us) =
        (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).map
          r.pos.add := by
    simpa using hlha_edgeVertices_translate r.pos HexReturnCoord.zero d
      (loopReverse us)
  have hfullnd := hlha_source_coord_nodup a h0 ts hsource
  have habsnd : (hlha_edgeVertices r.pos d (loopReverse us)).Nodup := by
    rw [habs]
    exact List.nodup_reverse.mpr hfullnd.take
  have hrelnd :
      (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).Nodup := by
    rw [htrans] at habsnd
    exact habsnd.of_map
  have hbehind : ∀ p ∈
      hlha_edgeVertices HexReturnCoord.zero d (loopReverse us),
      p.x - p.y ≤ 0 := by
    intro p hp
    have habsmem : r.pos.add p ∈
        hlha_edgeVertices r.pos d (loopReverse us) := by
      rw [htrans, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have hprevmem : r.pos.add p ∈
        (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).take
          (hexW2_cutPos 0 ts + 1) := by
      have : r.pos.add p ∈
          ((hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).take
            (hexW2_cutPos 0 ts + 1)).reverse := by
        rw [← habs]
        exact habsmem
      exact List.mem_reverse.mp this
    have hfullmem : r.pos.add p ∈
        hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts :=
      List.mem_of_mem_take hprevmem
    obtain ⟨k, hk, heq⟩ := hlha_mem_coordVertices
      HexReturnCoord.zero HexReturnCoord.base ts hfullmem
    have hmax := hlha_cut_latticeHeight_max ts hstd.1 k hk
    have hrheight : r.pos.x - r.pos.y =
        hlhr_latticeHeight ts (hexW2_cutPos 0 ts) := by
      rfl
    have hpheight : (r.pos.add p).x - (r.pos.add p).y =
        hlhr_latticeHeight ts k := by
      rw [heq]
      rfl
    simp only [HexReturnCoord.add] at hpheight
    omega
  have hrunit : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit HexReturnCoord.zero
      HexReturnCoord.base (ts.take (hexW2_cutPos 0 ts))
      HexReturnCoord.base_isUnit
    intro u hu
    exact hstd.1 u (List.mem_of_mem_take hu)
  have hdunit : d.IsUnit := hlha_negCoord_isUnit hrunit
  have hdmem : d ∈
      hlha_edgeVertices HexReturnCoord.zero d (loopReverse us) := by
    cases loopReverse us with
    | nil => simp [hlha_edgeVertices]
    | cons u vs =>
        simp only [hlha_edgeVertices, List.mem_cons]
        right
        simpa using hlha_edgeVertices_start_mem d (d.turn u) vs
  have hdheight := hbehind d hdmem
  exact ⟨hlha_awayDir_of_isUnit_of_height_nonpos d hdunit hdheight,
    hrevlegal, hrelnd, hbehind⟩


theorem hlha_prefixAugment_spec (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns 0 0 (hlha_prefixAugment ts)).IsLegalSAW ∧
      HLHRLiteralHalfSpace 0 (hlha_prefixAugment ts) ∧
      (hlha_prefixAugment ts).length =
        (ts.take (hexW2_cutPos 0 ts)).length + 1 := by
  unfold hlha_prefixAugment hlha_prefixReverseData
  generalize hp : ts.take (hexW2_cutPos 0 ts) = pre
  cases pre with
  | nil =>
      simp only
      refine ⟨hlha_emptyAugment_isLegalSAW,
        hlha_emptyAugment_halfSpace, ?_⟩
      simp [hlha_emptyAugment]
  | cons t us =>
      obtain ⟨hd, hlegal, hnodup, hbehind⟩ :=
        hlha_prefix_side_hypotheses a h0 ts hsource hp
      refine ⟨hlha_augmentSide_isLegalSAW _ _ hd hlegal hnodup hbehind,
        hlha_augmentSide_halfSpace _ _ hd hlegal hbehind, ?_⟩
      rw [hlha_augmentSide_length, loopReverse_length]
      simp


theorem hlha_halfStep_coord_neg_two :
    halfStep (-2) = (⟨-1, -1⟩ : HexReturnCoord).value * halfStep 0 := by
  have h0 : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have hm1 := hexReturn_halfStep_turn (halfStep 0) 0
    HexReturnCoord.base (-1) h0 (Or.inr rfl)
  have hm2 := hexReturn_halfStep_turn (halfStep 0) (-1)
    (HexReturnCoord.base.turn (-1)) (-1) hm1 (Or.inr rfl)
  simpa [HexReturnCoord.base, HexReturnCoord.turn,
    HexReturnCoord.right] using hm2

theorem hlha_halfStep_coord_neg_one :
    halfStep (-1) = (⟨0, -1⟩ : HexReturnCoord).value * halfStep 0 := by
  have h0 : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have hm1 := hexReturn_halfStep_turn (halfStep 0) 0
    HexReturnCoord.base (-1) h0 (Or.inr rfl)
  simpa [HexReturnCoord.base, HexReturnCoord.turn,
    HexReturnCoord.right] using hm1

theorem hlha_halfStep_coord_zero :
    halfStep 0 = (⟨1, 0⟩ : HexReturnCoord).value * halfStep 0 := by
  simp [HexReturnCoord.value]

theorem hlha_halfStep_coord_one :
    halfStep 1 = (⟨1, 1⟩ : HexReturnCoord).value * halfStep 0 := by
  have h0 : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have h1 := hexReturn_halfStep_turn (halfStep 0) 0
    HexReturnCoord.base 1 h0 (Or.inl rfl)
  simpa [HexReturnCoord.base, HexReturnCoord.turn,
    HexReturnCoord.left] using h1

theorem hlha_finalDirection_sum_mod (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (d : HexReturnCoord) (H : ℤ)
    (hfinal : (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = d)
    (hcoord : halfStep H = d.value * halfStep 0) :
    (6 : ℤ) ∣ (ts.sum - H) := by
  have hbase : halfStep 0 = HexReturnCoord.base.value * halfStep 0 := by simp
  have hgeom := (hlhr_coordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base 0 (halfStep 0) 0 ts hbase hlegal).2
  rw [hfinal, ← hcoord] at hgeom
  have hunit : hexUnit (hexInfra_headAccum 0 ts) = hexUnit H := by
    exact hexInfra_halfStep_inj hgeom
  have hmod := (hexUnit_eq_iff_mod _ _).mp hunit
  simpa [hexInfra_headAccum_eq_add_sum] using hmod

theorem hlha_reverseDir_mod_h1 (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hdir : hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨1, 1⟩) :
    (6 : ℤ) ∣ ts.sum - (-2) := by
  apply hlha_finalDirection_sum_mod ts hlegal ⟨-1, -1⟩ (-2)
  · have := congrArg hlha_negCoord hdir
    simpa using this
  · exact hlha_halfStep_coord_neg_two

theorem hlha_reverseDir_mod_h2 (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hdir : hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨0, 1⟩) :
    (6 : ℤ) ∣ ts.sum - (-1) := by
  apply hlha_finalDirection_sum_mod ts hlegal ⟨0, -1⟩ (-1)
  · have := congrArg hlha_negCoord hdir
    simpa using this
  · exact hlha_halfStep_coord_neg_one

theorem hlha_reverseDir_mod_h3 (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hdir : hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, 0⟩) :
    (6 : ℤ) ∣ ts.sum := by
  have h := hlha_finalDirection_sum_mod ts hlegal ⟨1, 0⟩ 0
    (by
      have hh := congrArg hlha_negCoord hdir
      simpa using hh)
    hlha_halfStep_coord_zero
  simpa using h

theorem hlha_reverseDir_mod_h4 (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hdir : hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, -1⟩) :
    (6 : ℤ) ∣ ts.sum - 1 := by
  apply hlha_finalDirection_sum_mod ts hlegal ⟨1, 1⟩ 1
  · have := congrArg hlha_negCoord hdir
    simpa using this
  · exact hlha_halfStep_coord_one

end StatMech.Universality
