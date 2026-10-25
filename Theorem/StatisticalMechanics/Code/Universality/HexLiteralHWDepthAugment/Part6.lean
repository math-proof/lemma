/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part5


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_neighbor_color_black {c d : HexAWCoord} {e : Fin 3}
    (hc : c.color = .black) (h : hexAWNeighbor c e = d) :
    d.color = .white := by
  subst d
  rcases c with ⟨i, j, color⟩
  cases color <;> simp_all
  fin_cases e <;> rfl

theorem hlhda_neighbor_color_white {c d : HexAWCoord} {e : Fin 3}
    (hc : c.color = .white) (h : hexAWNeighbor c e = d) :
    d.color = .black := by
  subst d
  rcases c with ⟨i, j, color⟩
  cases color <;> simp_all
  fin_cases e <;> rfl

theorem hlhda_cut_local {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ []) :
    let cp := hlhda_cutPos ts hleg
    (hlhc_prefixCoord ts hleg.1 (cp - 1)).color = .black ∧
      (hlhc_prefixCoord ts hleg.1 cp).color = .white ∧
      hlhd_depth ts hleg cp = hlhd_depth ts hleg (cp - 1) + 1 := by
  let cp := hlhda_cutPos ts hleg
  have hcpPos : 0 < cp := hlhda_cutPos_pos hleg hne
  have hcpLe : cp ≤ ts.length := hlhda_cutPos_le ts hleg
  have hklt : cp - 1 < ts.length := by omega
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg (cp - 1) hklt
  have hsucc : cp - 1 + 1 = cp := by omega
  have hstrict : hlhd_depth ts hleg (cp - 1) < hlhd_depth ts hleg cp :=
    hlhda_cutPos_first ts hleg (cp - 1) (by omega)
  have hcases := hlhd_neighbor_depth_cases
    (hlhc_prefixCoord ts hleg.1 (cp - 1)) e
  rw [he, hsucc] at hcases
  rcases hcases with hinc | hdec | hflat
  · exact ⟨hinc.2.1,
      hlhda_neighbor_color_black hinc.2.1 (he.trans (by rw [hsucc])),
      hinc.1⟩
  · unfold hlhd_depth at hstrict
    rw [hdec.1] at hstrict
    omega
  · unfold hlhd_depth at hstrict
    rw [hflat.1] at hstrict
    omega

theorem hlhda_coordRun_lastStep (p d : HexReturnCoord) (ts : List ℤ)
    {k : ℕ} (hk : 0 < k) (hkle : k ≤ ts.length) :
    (hlhr_coordRun p d (ts.take k)).pos =
      ((hlhr_coordRun p d (ts.take (k - 1))).pos.add
        (hlhr_coordRun p d (ts.take k)).dir) := by
  induction ts generalizing p d k with
  | nil => simp at hkle; omega
  | cons t ts ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero => simp [hlhr_coordRun]
          | succ k =>
              simp only [List.take_succ_cons, hlhr_coordRun, Nat.succ_sub_one]
              exact ih (p.add (d.turn t)) (d.turn t) (k := k + 1)
                (by omega) (by simpa using Nat.le_of_succ_le_succ hkle)

theorem hlhda_score_neg (p : HexReturnCoord) :
    hlhda_score (hlha_negCoord p) = -hlhda_score p := by
  cases p
  simp [hlhda_score, hlha_negCoord]
  ring

theorem hlhda_inward_of_unit_score_one (d : HexReturnCoord)
    (hu : d.IsUnit) (hs : hlhda_score d = 1) : HLHDAInwardDir d := by
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [HLHDAInwardDir, HexReturnCoord.base, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right, hlhda_score] at hs ⊢

theorem hlhda_cutState_inward {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ []) :
    HLHDAInwardDir (hlhda_cutState ts hleg).dir := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let rp := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
    (ts.take (cp - 1))
  have hcpPos : 0 < cp := hlhda_cutPos_pos hleg hne
  have hcpLe : cp ≤ ts.length := hlhda_cutPos_le ts hleg
  have hstep := hlhda_coordRun_lastStep HexReturnCoord.zero
    HexReturnCoord.base ts hcpPos hcpLe
  change r.pos = rp.pos.add r.dir at hstep
  have hrPos : r.pos =
      hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp) := by
    exact hlhda_prefixCoord_returnPos ts hleg cp
  have hpPos : rp.pos =
      hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (cp - 1)) := by
    exact hlhda_prefixCoord_returnPos ts hleg (cp - 1)
  have hlocal := hlhda_cut_local hleg hne
  change
    (hlhc_prefixCoord ts hleg.1 (cp - 1)).color = .black ∧
      (hlhc_prefixCoord ts hleg.1 cp).color = .white ∧
      hlhd_depth ts hleg cp = hlhd_depth ts hleg (cp - 1) + 1 at hlocal
  have hscoreCut := hlhda_returnScore_exact
    (hlhc_prefixCoord ts hleg.1 cp)
  have hscorePrev := hlhda_returnScore_exact
    (hlhc_prefixCoord ts hleg.1 (cp - 1))
  rw [hlocal.2.1] at hscoreCut
  rw [hlocal.1] at hscorePrev
  change hlhda_score (hexAWReturnPos
      (hlhc_prefixCoord ts hleg.1 cp)) =
        3 * hlhd_depth ts hleg cp - 2 at hscoreCut
  change hlhda_score (hexAWReturnPos
      (hlhc_prefixCoord ts hleg.1 (cp - 1))) =
        3 * hlhd_depth ts hleg (cp - 1) at hscorePrev
  have hs : hlhda_score r.dir = 1 := by
    have hadd := congrArg hlhda_score hstep
    rw [hlhda_score_add, hrPos, hpPos] at hadd
    rw [hscoreCut, hscorePrev] at hadd
    omega
  have hu : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit HexReturnCoord.zero
      HexReturnCoord.base (ts.take cp) HexReturnCoord.base_isUnit
    intro t ht
    exact hleg.1 t (List.mem_of_mem_take ht)
  exact hlhda_inward_of_unit_score_one r.dir hu hs

theorem hlhda_returnPos_normalize_down (source c : HexAWCoord)
    (hs : source.color = .white) :
    hexAWReturnPos (hlhd_normalizeCoord false source c) =
      (hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c)) := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases sc
  · simp at hs
  · cases color <;>
      simp [hlhd_normalizeCoord, hlhd_swapColor, hexAWReturnPos,
        HexReturnCoord.add, hlha_negCoord] <;> congr <;> omega

theorem hlhda_normalized_score_lower (source c : HexAWCoord)
    (hs : source.color = .white)
    (hdepth : hexAWDepth c ≤ hexAWDepth source) :
    -2 ≤ hlhda_score
      ((hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c))) := by
  rw [← hlhda_returnPos_normalize_down source c hs]
  have hd := hlhd_normalizeCoord_depth false source c
  simp only [Bool.false_eq_true, ↓reduceIte] at hd
  have hsExact := hlhda_returnScore_exact
    (hlhd_normalizeCoord false source c)
  unfold hlhda_score
  rw [hsExact, hd]
  split <;> omega

theorem hlhda_normalized_eq_flat_iff (source c : HexAWCoord)
    (hs : source.color = .white) :
    (hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c)) =
        hlhda_flatNeighbor ↔
      c = hexAWNeighbor source 0 := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases sc <;> cases color <;>
    simp_all [hexAWReturnPos, HexReturnCoord.add, hlha_negCoord,
      hlhda_flatNeighbor, hexAWNeighbor, HexReturnCoord.mk.injEq] <;> omega

@[simp] theorem hlhda_depth_neighbor_zero (c : HexAWCoord) :
    hexAWDepth (hexAWNeighbor c 0) = hexAWDepth c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> simp [hexAWNeighbor, hexAWDepth, hexAWLong]

theorem hlhda_add_neg_add (p q : HexReturnCoord) :
    p.add (hlha_negCoord (p.add q)) = hlha_negCoord q := by
  cases p
  cases q
  simp [HexReturnCoord.add, hlha_negCoord]

theorem hlhda_prefix_normalized_point {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hpre : ts.take (hlhda_cutPos ts hleg) = t :: us)
    {q : HexReturnCoord}
    (hq : q ∈ hlha_edgeVertices HexReturnCoord.zero
      (hlhda_cutState ts hleg).dir (loopReverse us)) :
    ∃ k, k ≤ hlhda_cutPos ts hleg ∧
      q = (hexAWReturnPos
          (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add
        (hlha_negCoord (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k))) := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := HexReturnCoord.base.turn t
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_take
    rw [hpre]
    simp
  have ht := hleg.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hutake : u ∈ ts.take (hlhda_cutPos ts hleg) := by
      rw [hpre]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_take hutake)
  have hrevLegal : ∀ u ∈ loopReverse us, u = 1 ∨ u = -1 :=
    loopReverse_legal us hus
  have hrstate :
      hlhr_coordRun (HexReturnCoord.zero.add d0) d0 us = r := by
    dsimp [r, hlhda_cutState, d0]
    rw [hpre]
    simp only [hlhr_coordRun]
  have hrev := hlha_edgeVertices_loopReverse HexReturnCoord.zero d0 us hus
  rw [hrstate] at hrev
  have hneg := hlha_edgeVertices_neg HexReturnCoord.zero
    (hlha_negCoord r.dir) (loopReverse us) hrevLegal
  simp only [hlha_negCoord_zero, hlha_negCoord_negCoord] at hneg
  rw [hneg, List.mem_map] at hq
  obtain ⟨p, hp, hqp⟩ := hq
  have htrans := hlha_edgeVertices_translate r.pos HexReturnCoord.zero
    (hlha_negCoord r.dir) (loopReverse us)
  simp only [hlha_add_zero] at htrans
  have habs : r.pos.add p ∈
      hlha_edgeVertices r.pos (hlha_negCoord r.dir) (loopReverse us) := by
    rw [htrans, List.mem_map]
    exact ⟨p, hp, rfl⟩
  rw [hrev.1, List.mem_reverse] at habs
  have hforward : hlha_edgeVertices HexReturnCoord.zero d0 us =
      hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        (ts.take cp) := by
    rw [hpre, hlha_coordVertices_cons_eq_edge]
  rw [hforward] at habs
  obtain ⟨k, hk, hkpos⟩ := hlha_mem_coordVertices
    HexReturnCoord.zero HexReturnCoord.base (ts.take cp) habs
  have hpreLen : (ts.take cp).length = cp := by
    rw [List.length_take_of_le (hlhda_cutPos_le ts hleg)]
  rw [hpreLen] at hk
  have htake : (ts.take cp).take k = ts.take k := by
    rw [List.take_take, Nat.min_eq_left hk]
  rw [htake] at hkpos
  have hkReturn := hlhda_prefixCoord_returnPos ts hleg k
  have hcpReturn := hlhda_prefixCoord_returnPos ts hleg cp
  refine ⟨k, hk, ?_⟩
  rw [← hkReturn, ← hcpReturn, ← hqp, ← hkpos]
  change hlha_negCoord p = r.pos.add (hlha_negCoord (r.pos.add p))
  exact (hlhda_add_neg_add r.pos p).symm

theorem hlhda_prefix_side_hypotheses {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ [])
    {t : ℤ} {us : List ℤ}
    (hpre : ts.take (hlhda_cutPos ts hleg) = t :: us) :
    let d := (hlhda_cutState ts hleg).dir
    HLHDAInwardDir d ∧
      (∀ u ∈ loopReverse us, u = 1 ∨ u = -1) ∧
      (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).Nodup ∧
      (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d (loopReverse us),
        -2 ≤ hlhda_score q) ∧
      hlhda_flatNeighbor ∉
        hlha_edgeVertices HexReturnCoord.zero d (loopReverse us) := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := HexReturnCoord.base.turn t
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_take
    rw [hpre]
    simp
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hutake : u ∈ ts.take (hlhda_cutPos ts hleg) := by
      rw [hpre]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_take hutake)
  have hrevLegal : ∀ u ∈ loopReverse us, u = 1 ∨ u = -1 :=
    loopReverse_legal us hus
  have hrstate :
      hlhr_coordRun (HexReturnCoord.zero.add d0) d0 us = r := by
    dsimp [r, hlhda_cutState, d0]
    rw [hpre]
    simp only [hlhr_coordRun]
  have hrev := hlha_edgeVertices_loopReverse HexReturnCoord.zero d0 us hus
  rw [hrstate] at hrev
  have hforward : hlha_edgeVertices HexReturnCoord.zero d0 us =
      hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base
        (ts.take cp) := by
    rw [hpre, hlha_coordVertices_cons_eq_edge]
  have hfullNodup := hlha_source_coord_nodup hexAWStart 1 ts hleg
  have hforwardNodup :
      (hlha_edgeVertices HexReturnCoord.zero d0 us).Nodup := by
    rw [hforward, hlha_coordVertices_take]
    exact hfullNodup.take
  have habsNodup :
      (hlha_edgeVertices r.pos (hlha_negCoord r.dir)
        (loopReverse us)).Nodup := by
    rw [hrev.1]
    exact List.nodup_reverse.mpr hforwardNodup
  have htrans := hlha_edgeVertices_translate r.pos HexReturnCoord.zero
    (hlha_negCoord r.dir) (loopReverse us)
  simp only [hlha_add_zero] at htrans
  have hrelNodup :
      (hlha_edgeVertices HexReturnCoord.zero (hlha_negCoord r.dir)
        (loopReverse us)).Nodup := by
    rw [htrans] at habsNodup
    exact habsNodup.of_map
  have hneg := hlha_edgeVertices_neg HexReturnCoord.zero
    (hlha_negCoord r.dir) (loopReverse us) hrevLegal
  simp only [hlha_negCoord_zero, hlha_negCoord_negCoord] at hneg
  have hnormNodup :
      (hlha_edgeVertices HexReturnCoord.zero r.dir
        (loopReverse us)).Nodup := by
    rw [hneg]
    exact hrelNodup.map hlha_negCoord_injective
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  change (hlhc_prefixCoord ts hleg.1 cp).color = .white at hcutWhite
  have hscore : ∀ q ∈ hlha_edgeVertices HexReturnCoord.zero r.dir
      (loopReverse us), -2 ≤ hlhda_score q := by
    intro q hq
    obtain ⟨k, hk, hqeq⟩ :=
      hlhda_prefix_normalized_point hleg hpre hq
    rw [hqeq]
    apply hlhda_normalized_score_lower _ _ hcutWhite
    exact hlhda_cutPos_max ts hleg k
      (le_trans hk (hlhda_cutPos_le ts hleg))
  have hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero r.dir (loopReverse us) := by
    intro hmem
    obtain ⟨k, hk, hqeq⟩ :=
      hlhda_prefix_normalized_point hleg hpre hmem
    have hneighbor := (hlhda_normalized_eq_flat_iff
      (hlhc_prefixCoord ts hleg.1 cp)
      (hlhc_prefixCoord ts hleg.1 k) hcutWhite).mp hqeq.symm
    have hdepthEq : hlhd_depth ts hleg k = hlhd_depth ts hleg cp := by
      unfold hlhd_depth
      rw [hneighbor, hlhda_depth_neighbor_zero]
    have hklt : k < cp := by
      apply lt_of_le_of_ne hk
      intro hkeq
      subst k
      have hz := hlha_add_neg_self
        (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp))
      rw [hz] at hqeq
      exact (by decide : hlhda_flatNeighbor ≠ HexReturnCoord.zero) hqeq
    have hfirst := hlhda_cutPos_first ts hleg k hklt
    change hlhd_depth ts hleg k < hlhd_depth ts hleg cp at hfirst
    omega
  exact ⟨hlhda_cutState_inward hleg hne, hrevLegal, hnormNodup,
    hscore, hflat⟩

end
end StatMech.Universality
