/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part6


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_prefixAugment_isLegalSAW (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1 (hlhda_prefixAugment ts hleg)).IsLegalSAW := by
  unfold hlhda_prefixAugment
  split
  · exact hlhda_emptySide_isLegalSAW
  · rename_i t us hpre
    have hne : ts ≠ [] := by
      intro hnil
      simp [hnil] at hpre
    obtain ⟨hd, hlegal, hnodup, hscore, hflat⟩ :=
      hlhda_prefix_side_hypotheses hleg hne hpre
    exact hlhda_augmentSide_isLegalSAW _ _ hd hlegal hnodup hscore hflat

theorem hlhda_prefixAugment_halfSpace (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    HLHDLiteralHalfSpace (hlhda_prefixAugment ts hleg)
      (hlhda_prefixAugment_isLegalSAW ts hleg) := by
  by_cases hpre : ts.take (hlhda_cutPos ts hleg) = []
  · have hout : hlhda_prefixAugment ts hleg = hlhda_emptySide := by
      unfold hlhda_prefixAugment
      split <;> simp_all
    exact hlhda_halfSpace_congr hout.symm hlhda_emptySide_halfSpace
  · obtain ⟨t, us, hpreEq⟩ := List.exists_cons_of_ne_nil hpre
    have hout : hlhda_prefixAugment ts hleg =
        hlhda_augmentSide (hlhda_cutState ts hleg).dir
          (loopReverse us) := by
      unfold hlhda_prefixAugment
      split <;> simp_all
    have hne : ts ≠ [] := by
      intro hnil
      simp [hnil] at hpreEq
    obtain ⟨hd, hlegal, hnodup, hscore, hflat⟩ :=
      hlhda_prefix_side_hypotheses hleg hne hpreEq
    apply hlhda_halfSpace_congr hout.symm
    exact hlhda_augmentSide_halfSpace _ _ hd hlegal hnodup hscore hflat

theorem hlhda_prefixAugment_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_prefixAugment ts hleg).length = hlhda_cutPos ts hleg + 2 := by
  unfold hlhda_prefixAugment
  split
  · rename_i hpre
    have hlen := congrArg List.length hpre
    simp only [List.length_take, List.length_nil] at hlen
    have hcple := hlhda_cutPos_le ts hleg
    simp only [hlhda_emptySide_length]
    omega
  · rename_i t us hpre
    rw [hlhda_augmentSide_length]
    have hlen := congrArg List.length hpre
    rw [List.length_take_of_le (hlhda_cutPos_le ts hleg)] at hlen
    simp only [List.length_cons] at hlen
    simp [loopReverse]
    omega

theorem hlhda_prefixAugment_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1 (hlhda_prefixAugment ts hleg)).IsLegalSAW ∧
      HLHDLiteralHalfSpace (hlhda_prefixAugment ts hleg)
        (hlhda_prefixAugment_isLegalSAW ts hleg) ∧
      (hlhda_prefixAugment ts hleg).length =
        hlhda_cutPos ts hleg + 2 :=
  ⟨hlhda_prefixAugment_isLegalSAW ts hleg,
    hlhda_prefixAugment_halfSpace ts hleg,
    hlhda_prefixAugment_length ts hleg⟩


theorem hlhda_coordVertices_getElem (p d : HexReturnCoord) (ts : List ℤ)
    (k : ℕ) (hk : k ≤ ts.length) :
    (hlha_coordVertices p d ts)[k]'(by
      rw [hlha_coordVertices_length]
      omega) = (hlhr_coordRun p d (ts.take k)).pos := by
  induction ts generalizing p d k with
  | nil =>
      have hk0 : k = 0 := by simpa using hk
      subst k
      simp [hlha_coordVertices, hlhr_coordRun]
  | cons t ts ih =>
      cases k with
      | zero => simp [hlha_coordVertices, hlhr_coordRun]
      | succ k =>
          simp only [hlha_coordVertices, List.getElem_cons_succ,
            List.take_succ_cons, hlhr_coordRun]
          exact ih (p.add (d.turn t)) (d.turn t) k (by
            simp only [List.length_cons] at hk
            omega)

theorem hlhda_prefixCoord_injective (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {k l : ℕ} (hk : k ≤ ts.length) (hl : l ≤ ts.length)
    (heq : hlhc_prefixCoord ts hleg.1 k =
      hlhc_prefixCoord ts hleg.1 l) : k = l := by
  let vs := hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts
  have hnd : vs.Nodup := hlha_source_coord_nodup hexAWStart 1 ts hleg
  have hklen : k < vs.length := by
    dsimp [vs]
    rw [hlha_coordVertices_length]
    omega
  have hllen : l < vs.length := by
    dsimp [vs]
    rw [hlha_coordVertices_length]
    omega
  apply (hnd.getElem_inj_iff (hi := hklen) (hj := hllen)).mp
  rw [hlhda_coordVertices_getElem _ _ _ k hk,
    hlhda_coordVertices_getElem _ _ _ l hl,
    hlhda_prefixCoord_returnPos ts hleg k,
    hlhda_prefixCoord_returnPos ts hleg l, heq]

theorem hlhda_cut_next_state {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us) :
    hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (ts.take (hlhda_cutPos ts hleg + 1)) =
      let r := hlhda_cutState ts hleg
      ⟨r.pos.add (r.dir.turn t), r.dir.turn t⟩ := by
  let cp := hlhda_cutPos ts hleg
  have hcplt : cp < ts.length := by
    have hlen := congrArg List.length hsuf
    simp only [List.length_drop, List.length_cons] at hlen
    omega
  have hdrop := List.drop_eq_getElem_cons hcplt
  rw [hsuf] at hdrop
  have htget : ts[cp] = t := by
    exact List.cons.inj hdrop |>.1.symm
  have htake := List.take_concat_get' ts cp hcplt
  rw [htget] at htake
  rw [← htake, hlha_coordRun_append]
  simp [hlhda_cutState, cp, hlhr_coordRun]

theorem hlhda_normalized_neighbor_cases (source : HexAWCoord)
    (hs : source.color = .white) (e : Fin 3) :
    let q := (hexAWReturnPos source).add
      (hlha_negCoord (hexAWReturnPos (hexAWNeighbor source e)))
    q = hlhda_flatNeighbor ∨ HLHDAInwardDir q := by
  rcases source with ⟨i, j, color⟩
  cases color <;> simp_all
  fin_cases e <;>
    simp [hexAWReturnPos, hexAWNeighbor, HexReturnCoord.add,
      hlha_negCoord, hlhda_flatNeighbor, HLHDAInwardDir,
      HexReturnCoord.base, HexReturnCoord.turn, HexReturnCoord.left,
      HexReturnCoord.right] <;> ring

theorem hlhda_suffix_normalized_point {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
    {q : HexReturnCoord}
    (hq : q ∈ hlha_edgeVertices HexReturnCoord.zero
      (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us) :
    ∃ k, k ≤ ts.length ∧
      q = (hexAWReturnPos
          (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add
        (hlha_negCoord (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k))) := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := r.dir.turn t
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_drop
    rw [hsuf]
    simp
  have ht := hleg.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hudrop : u ∈ ts.drop (hlhda_cutPos ts hleg) := by
      rw [hsuf]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_drop hudrop)
  have hneg := hlha_edgeVertices_neg HexReturnCoord.zero d0 us hus
  simp only [hlha_negCoord_zero] at hneg
  rw [hneg, List.mem_map] at hq
  obtain ⟨p, hp, hqp⟩ := hq
  have hdrop := hlha_coordVertices_drop HexReturnCoord.zero
    HexReturnCoord.base ts cp (hlhda_cutPos_le ts hleg)
  rw [hsuf] at hdrop
  change hlha_coordVertices r.pos r.dir (t :: us) = _ at hdrop
  rw [hlha_coordVertices_cons_eq_edge] at hdrop
  change hlha_edgeVertices r.pos d0 us = _ at hdrop
  have htrans := hlha_edgeVertices_translate r.pos HexReturnCoord.zero d0 us
  simp only [hlha_add_zero] at htrans
  have habs : r.pos.add p ∈
      hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts := by
    apply List.mem_of_mem_drop
    rw [← hdrop, htrans, List.mem_map]
    exact ⟨p, hp, rfl⟩
  obtain ⟨k, hk, hkpos⟩ := hlha_mem_coordVertices
    HexReturnCoord.zero HexReturnCoord.base ts habs
  have hkReturn := hlhda_prefixCoord_returnPos ts hleg k
  have hcpReturn := hlhda_prefixCoord_returnPos ts hleg cp
  refine ⟨k, hk, ?_⟩
  rw [← hkReturn, ← hcpReturn, ← hqp, ← hkpos]
  change hlha_negCoord p = r.pos.add (hlha_negCoord (r.pos.add p))
  exact (hlhda_add_neg_add r.pos p).symm

theorem hlhda_suffix_flat_forces_terminal {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ [])
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
    (hflat : hlhda_flatNeighbor ∈
      hlha_edgeVertices HexReturnCoord.zero
        (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us) :
    us = [] := by
  let cp := hlhda_cutPos ts hleg
  let cut := hlhc_prefixCoord ts hleg.1 cp
  obtain ⟨k, hk, hkflat⟩ :=
    hlhda_suffix_normalized_point hleg hsuf hflat
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  change cut.color = .white at hcutWhite
  have hkCoord : hlhc_prefixCoord ts hleg.1 k = hexAWNeighbor cut 0 :=
    (hlhda_normalized_eq_flat_iff cut
      (hlhc_prefixCoord ts hleg.1 k) hcutWhite).mp hkflat.symm
  have hkDepth : hlhd_depth ts hleg k = hlhd_depth ts hleg cp := by
    unfold hlhd_depth
    rw [hkCoord, hlhda_depth_neighbor_zero]
  have hcpLe := hlhda_cutPos_le ts hleg
  have hkgt : cp < k := by
    rcases lt_trichotomy k cp with hlt | heq | hgt
    · have hfirst := hlhda_cutPos_first ts hleg k hlt
      change hlhd_depth ts hleg k < hlhd_depth ts hleg cp at hfirst
      omega
    · subst k
      exact (hexAWNeighbor_ne cut 0 hkCoord.symm).elim
    · exact hgt
  have hkPos : 0 < k := lt_trans (hlhda_cutPos_pos hleg hne) hkgt
  have hkm1lt : k - 1 < ts.length := by omega
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg (k - 1) hkm1lt
  have hksucc : k - 1 + 1 = k := by omega
  rw [hksucc, hkCoord] at he
  have hback := congrArg (fun c => hexAWNeighbor c e) he
  simp only [hexAWNeighbor_invol] at hback
  have hcases := hlhd_neighbor_depth_cases (hexAWNeighbor cut 0) e
  have hprevMax := hlhda_cutPos_max ts hleg (k - 1) (by omega)
  change hlhd_depth ts hleg (k - 1) ≤ hlhd_depth ts hleg cp at hprevMax
  have hprevCoord : hlhc_prefixCoord ts hleg.1 (k - 1) = cut := by
    rcases hcases with hinc | hdec | hzero
    · have hdepthInc : hlhd_depth ts hleg (k - 1) =
          hlhd_depth ts hleg cp + 1 := by
        unfold hlhd_depth
        rw [hback, hinc.1, hlhda_depth_neighbor_zero]
      omega
    · have hblack : (hexAWNeighbor cut 0).color = .black :=
        hlhda_neighbor_color_white hcutWhite rfl
      have hcolor := hdec.2.1
      rw [hblack] at hcolor
      cases hcolor
    · rw [hzero.2] at hback
      simpa using hback
  have hkm1 : k - 1 = cp :=
    hlhda_prefixCoord_injective ts hleg (by omega) hcpLe hprevCoord
  have hkEq : k = cp + 1 := by omega
  have hkLast : k = ts.length := by
    by_contra hneLast
    have hklt : k < ts.length := by omega
    obtain ⟨f, hf⟩ := hlhc_prefixCoord_adjacent ts hleg k hklt
    rw [hkCoord] at hf
    have hfcases := hlhd_neighbor_depth_cases (hexAWNeighbor cut 0) f
    have hnextMax := hlhda_cutPos_max ts hleg (k + 1) (by omega)
    change hlhd_depth ts hleg (k + 1) ≤ hlhd_depth ts hleg cp at hnextMax
    rcases hfcases with hinc | hdec | hzero
    · have hnextDepth : hlhd_depth ts hleg (k + 1) =
          hlhd_depth ts hleg cp + 1 := by
        unfold hlhd_depth
        rw [← hf, hinc.1, hlhda_depth_neighbor_zero]
      omega
    · have hblack : (hexAWNeighbor cut 0).color = .black :=
        hlhda_neighbor_color_white hcutWhite rfl
      have hcolor := hdec.2.1
      rw [hblack] at hcolor
      cases hcolor
    · have hnextCut : hlhc_prefixCoord ts hleg.1 (k + 1) = cut := by
        rw [hzero.2] at hf
        simpa using hf.symm
      have : k + 1 = cp :=
        hlhda_prefixCoord_injective ts hleg (by omega) hcpLe hnextCut
      omega
  have hsufLen := congrArg List.length hsuf
  simp only [List.length_drop, List.length_cons] at hsufLen
  have husLen : us.length = 0 := by omega
  exact List.length_eq_zero_iff.mp husLen

theorem hlhda_inward_empty_hypotheses (d : HexReturnCoord)
    (hd : HLHDAInwardDir d) :
    (hlha_edgeVertices HexReturnCoord.zero d []).Nodup ∧
      (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d [],
        -2 ≤ hlhda_score q) ∧
      hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d [] := by
  rcases hd with hd | hd <;> rw [hd] <;>
    simp [hlha_edgeVertices, HexReturnCoord.zero, HexReturnCoord.base,
      HexReturnCoord.turn, HexReturnCoord.left, HexReturnCoord.right,
      HexReturnCoord.add, hlhda_score, hlhda_flatNeighbor]

theorem hlhda_suffix_side_hypotheses {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
    (hnotFlat : hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) ≠
      hlhda_flatNeighbor) :
    let d := hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)
    HLHDAInwardDir d ∧
      (∀ u ∈ us, u = 1 ∨ u = -1) ∧
      (hlha_edgeVertices HexReturnCoord.zero d us).Nodup ∧
      (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d us,
        -2 ≤ hlhda_score q) ∧
      hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d us := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := r.dir.turn t
  let d := hlha_negCoord d0
  have hne : ts ≠ [] := by
    intro hnil
    simp [hnil] at hsuf
  have htmem : t ∈ ts := by
    apply List.mem_of_mem_drop
    rw [hsuf]
    simp
  have ht := hleg.1 t htmem
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hudrop : u ∈ ts.drop (hlhda_cutPos ts hleg) := by
      rw [hsuf]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_drop hudrop)
  have hdrop := hlha_coordVertices_drop HexReturnCoord.zero
    HexReturnCoord.base ts cp (hlhda_cutPos_le ts hleg)
  rw [hsuf] at hdrop
  change hlha_coordVertices r.pos r.dir (t :: us) = _ at hdrop
  rw [hlha_coordVertices_cons_eq_edge] at hdrop
  change hlha_edgeVertices r.pos d0 us = _ at hdrop
  have habsNodup : (hlha_edgeVertices r.pos d0 us).Nodup := by
    rw [hdrop]
    exact (hlha_source_coord_nodup hexAWStart 1 ts hleg).drop
  have htrans := hlha_edgeVertices_translate r.pos HexReturnCoord.zero d0 us
  simp only [hlha_add_zero] at htrans
  have hrelNodup :
      (hlha_edgeVertices HexReturnCoord.zero d0 us).Nodup := by
    rw [htrans] at habsNodup
    exact habsNodup.of_map
  have hneg := hlha_edgeVertices_neg HexReturnCoord.zero d0 us hus
  simp only [hlha_negCoord_zero] at hneg
  have hnormNodup :
      (hlha_edgeVertices HexReturnCoord.zero d us).Nodup := by
    change (hlha_edgeVertices HexReturnCoord.zero
      (hlha_negCoord d0) us).Nodup
    rw [hneg]
    exact hrelNodup.map hlha_negCoord_injective
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  change (hlhc_prefixCoord ts hleg.1 cp).color = .white at hcutWhite
  have hscore : ∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d us,
      -2 ≤ hlhda_score q := by
    intro q hq
    obtain ⟨k, hk, hqeq⟩ := hlhda_suffix_normalized_point hleg hsuf hq
    rw [hqeq]
    apply hlhda_normalized_score_lower _ _ hcutWhite
    exact hlhda_cutPos_max ts hleg k hk
  have hflat : hlhda_flatNeighbor ∉
      hlha_edgeVertices HexReturnCoord.zero d us := by
    intro hmem
    have husNil := hlhda_suffix_flat_forces_terminal hleg hne hsuf hmem
    subst us
    simp [hlha_edgeVertices, hlha_zero_add] at hmem
    rcases hmem with hzero | hdflat
    · exact (by decide : HexReturnCoord.zero ≠ hlhda_flatNeighbor) hzero.symm
    · exact hnotFlat hdflat.symm
  have hcplt : cp < ts.length := by
    have hlen := congrArg List.length hsuf
    simp only [List.length_drop, List.length_cons] at hlen
    omega
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg cp hcplt
  have hnext := hlhda_cut_next_state hleg hsuf
  have hnextPos := congrArg HLHRCoordRun.pos hnext
  have hrPos := hlhda_prefixCoord_returnPos ts hleg cp
  change r.pos = hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp) at hrPos
  have hnPos := hlhda_prefixCoord_returnPos ts hleg (cp + 1)
  have hdCoord : d =
      (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp)).add
        (hlha_negCoord
          (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (cp + 1)))) := by
    change hlha_negCoord d0 = _
    change (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
      (ts.take (cp + 1))).pos = r.pos.add d0 at hnextPos
    rw [hnPos, hrPos] at hnextPos
    rw [hnextPos, ← hrPos]
    exact (hlhda_add_neg_add r.pos d0).symm
  have hdirCases := hlhda_normalized_neighbor_cases
    (hlhc_prefixCoord ts hleg.1 cp) hcutWhite e
  rw [he] at hdirCases
  change _ = hlhda_flatNeighbor ∨ HLHDAInwardDir _ at hdirCases
  rw [← hdCoord] at hdirCases
  have hdInward : HLHDAInwardDir d := hdirCases.resolve_left hnotFlat
  exact ⟨hdInward, hus, hnormNodup, hscore, hflat⟩

end
end StatMech.Universality
