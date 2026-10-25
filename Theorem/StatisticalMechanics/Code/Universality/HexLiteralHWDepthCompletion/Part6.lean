/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part5


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem HLHDAEndpointColumnWalk.prefix_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHDAEndpointColumnWalk T ts)
    {k : ℕ} (hk : k < ts.length) :
    hlhc_prefixCoord ts W.legal.1 k ∈
      hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  refine ⟨(W.horizontal k hk).1, (W.horizontal k hk).2, ?_, ?_⟩
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n =>
            hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 n))
            (Finset.mem_range.mpr hk))
          (Nat.le_max_left _ _))
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by
        exact_mod_cast le_trans
          (Finset.le_sup (f := fun n =>
            hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 n))
            (Finset.mem_range.mpr hk))
          (Nat.le_max_left _ _))

theorem HLHDAEndpointColumnWalk.top_mem_vertexSet
    {T : ℕ} {ts : List ℤ} (W : HLHDAEndpointColumnWalk T ts)
    (hT : 0 < T) :
    W.topCoord ∈ hexCSVertexSet T W.stripHeight := by
  rw [hexCS_mem_vertexSet_iff]
  have hbook : hexAWBookRe2 W.topCoord = 3 * T - 1 := by
    simp [hexAWBookRe2, W.top_white, W.top_depth]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hbook]
    omega
  · rw [hbook]
    omega
  · exact le_trans (hlhc_coord_le_bound_i _)
      (by exact_mod_cast Nat.le_max_right _ _)
  · exact le_trans (hlhc_coord_le_bound_j _)
      (by exact_mod_cast Nat.le_max_right _ _)

theorem HLHDAEndpointColumnWalk.mem_topAtWidth
    {T : ℕ} {ts : List ℤ} (W : HLHDAEndpointColumnWalk T ts)
    (hT : 0 < T) : HexCSTopWalkAtWidth T hT ts := by
  refine ⟨W.stripHeight, W.legal, ?_, W.topCoord,
    W.top_mem_vertexSet hT, W.top_white, W.top_depth, W.endsAt⟩
  intro z hz
  unfold HexWalk.mids at hz
  change z ∈ midsAux hexAWStart 1 ts at hz
  rw [List.mem_iff_getElem] at hz
  obtain ⟨k, hklen, hkz⟩ := hz
  have hkle : k ≤ ts.length := by
    rw [length_midsAux] at hklen
    omega
  have hget := hexJordan_midsAux_getElem?_eq hexAWStart 1 ts k hkle
  rw [List.getElem?_eq_getElem hklen, Option.some.injEq] at hget
  have hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) = z :=
    hget.symm.trans hkz
  change z ∈ hexCSMids T W.stripHeight
  by_cases hk : k < ts.length
  · obtain ⟨e, he⟩ := hlhc_prefixCoord_mid_incident ts W.legal.1 k
    rw [← hmid, hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨hlhc_prefixCoord ts W.legal.1 k,
      W.prefix_mem_vertexSet hk⟩, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e, Finset.mem_univ _, he.symm⟩
  · have hkeq : k = ts.length := by omega
    have hzTop : z = hexAWMid W.topCoord 0 := by
      rw [← hmid, hkeq, List.take_length]
      rw [← hexInfra_endMid_eq_midAccum hexAWStart 1 ts]
      exact W.endsAt
    rw [hzTop, hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨W.topCoord, W.top_mem_vertexSet hT⟩,
      Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, rfl⟩

theorem hlhda_prefixCoord_eq_of_take_eq
    {xs ys : List ℤ}
    (hx : (ofTurns hexAWStart 1 xs).LegalTurns)
    (hy : (ofTurns hexAWStart 1 ys).LegalTurns)
    (k : ℕ) (htake : xs.take k = ys.take k) :
    hlhc_prefixCoord xs hx k = hlhc_prefixCoord ys hy k := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex xs hx k,
    ← hlhc_prefixCoord_vertex ys hy k, htake]

theorem hlhda_prefixCoord_append_of_le
    (xs tail : List ℤ)
    (hx : (ofTurns hexAWStart 1 xs).LegalTurns)
    (hout : (ofTurns hexAWStart 1 (xs ++ tail)).LegalTurns)
    {k : ℕ} (hk : k ≤ xs.length) :
    hlhc_prefixCoord (xs ++ tail) hout k = hlhc_prefixCoord xs hx k := by
  apply hlhda_prefixCoord_eq_of_take_eq
  rw [List.take_append_of_le_length hk]


theorem hlhda_coordRun_translate_pos (q p d : HexReturnCoord)
    (ws : List ℤ) :
    (hlhr_coordRun (q.add p) d ws).pos =
      q.add (hlhr_coordRun p d ws).pos := by
  induction ws generalizing p d with
  | nil => rfl
  | cons t ws ih =>
      simp only [hlhr_coordRun]
      rw [show (q.add p).add (d.turn t) = q.add (p.add (d.turn t)) by
        cases q
        cases p
        cases d
        simp [HexReturnCoord.add]
        constructor <;> omega]
      exact ih (p.add (d.turn t)) (d.turn t)

theorem hlhda_add_neg_left (p q : HexReturnCoord) :
    p.add ((hlha_negCoord p).add q) = q := by
  cases p
  cases q
  simp [HexReturnCoord.add, hlha_negCoord]

theorem hlhda_coordRun_neg_pos (p d : HexReturnCoord) (ws : List ℤ)
    (hlegal : ∀ t ∈ ws, t = 1 ∨ t = -1) :
    (hlhr_coordRun (hlha_negCoord p) (hlha_negCoord d) ws).pos =
      hlha_negCoord (hlhr_coordRun p d ws).pos := by
  induction ws generalizing p d with
  | nil => rfl
  | cons t ws ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ws, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simp only [hlhr_coordRun]
      rw [← hlha_negCoord_turn d ht, ← hlha_negCoord_add]
      exact ih (p.add (d.turn t)) (d.turn t) htail

theorem hlhda_coordRun_augmentSide_pos (d : HexReturnCoord)
    (internal : List ℤ) (hd : HLHDAInwardDir d) :
    (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
      (hlhda_augmentSide d internal)).pos =
        hlhda_spacerRoot.add
          (hlhr_coordRun (HexReturnCoord.zero.add d) d internal).pos := by
  rw [show hlhda_augmentSide d internal =
      (-1 : ℤ) :: 1 :: hlhda_entryTurn d :: internal by
    simp [hlhda_augmentSide]]
  simp only [hlhr_coordRun]
  change (hlhr_coordRun
    (hlhda_spacerRoot.add
      (HexReturnCoord.base.turn (hlhda_entryTurn d)))
    (HexReturnCoord.base.turn (hlhda_entryTurn d)) internal).pos = _
  rw [hlhda_entryTurn_dir hd]
  rw [show hlhda_spacerRoot.add d =
      hlhda_spacerRoot.add (HexReturnCoord.zero.add d) by
    simp]
  exact hlhda_coordRun_translate_pos hlhda_spacerRoot
    (HexReturnCoord.zero.add d) d internal

theorem hlhda_spacer_normalized_depth_color
    (source c out : HexAWCoord) (hsource : source.color = .white)
    (hpos : hexAWReturnPos out =
      hlhda_spacerRoot.add
        ((hexAWReturnPos source).add
          (hlha_negCoord (hexAWReturnPos c)))) :
    out.color = hlhd_swapColor c.color ∧
      hexAWDepth out = hexAWDepth source - hexAWDepth c + 1 := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  rcases out with ⟨oi, oj, outColor⟩
  cases sc <;> cases color <;> cases outColor <;>
    simp_all [hexAWReturnPos, hlhda_spacerRoot, HexReturnCoord.add,
      hlha_negCoord, hlhd_swapColor, hexAWDepth, hexAWLong,
      HexReturnCoord.mk.injEq] <;> omega

theorem hlhda_spacerWhite_depth (c : HexAWCoord)
    (hpos : hexAWReturnPos c = hlhda_spacerWhite) :
    c.color = .white ∧ hexAWDepth c = 1 := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp_all [hexAWReturnPos, hlhda_spacerWhite, hexAWDepth, hexAWLong,
      HexReturnCoord.mk.injEq] <;> omega

theorem hlhda_augmentSide_depth_bounds
    (d : HexReturnCoord) (internal : List ℤ) (hd : HLHDAInwardDir d)
    (hraw : (ofTurns hexAWStart 1
      (hlhda_augmentSide d internal)).IsLegalSAW)
    (source : HexAWCoord) (hsourceWhite : source.color = .white)
    (M : ℕ) (hsourceDepth : hexAWDepth source = M)
    (hnormalized : ∀ q ∈
      hlha_edgeVertices HexReturnCoord.zero d internal,
      ∃ c : HexAWCoord,
        0 ≤ hexAWDepth c ∧ hexAWDepth c ≤ M ∧
          q = (hexAWReturnPos source).add
            (hlha_negCoord (hexAWReturnPos c))) :
    ∀ j, j ≤ (hlhda_augmentSide d internal).length →
      0 ≤ hlhd_depth (hlhda_augmentSide d internal) hraw j ∧
        hlhd_depth (hlhda_augmentSide d internal) hraw j ≤ M + 1 := by
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [hlhda_depth_zero]
    omega
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hmem := hlha_coordRun_take_mem_tail HexReturnCoord.zero
      HexReturnCoord.base (hlhda_augmentSide d internal) hjpos hj
    rw [hlhda_prefixCoord_returnPos
      (hlhda_augmentSide d internal) hraw j] at hmem
    rw [hlhda_coordVertices_augmentSide d internal hd] at hmem
    simp only [List.tail_cons, List.mem_cons, List.mem_map] at hmem
    rcases hmem with hspacer | ⟨q, hq, hqeq⟩
    · have hs := hlhda_spacerWhite_depth
        (hlhc_prefixCoord (hlhda_augmentSide d internal) hraw.1 j)
        hspacer
      change 0 ≤ hexAWDepth
          (hlhc_prefixCoord (hlhda_augmentSide d internal) hraw.1 j) ∧
        hexAWDepth
          (hlhc_prefixCoord (hlhda_augmentSide d internal) hraw.1 j) ≤
            M + 1
      omega
    · obtain ⟨c, hc0, hcM, hqnorm⟩ := hnormalized q hq
      have hgeom := hlhda_spacer_normalized_depth_color source c
        (hlhc_prefixCoord (hlhda_augmentSide d internal) hraw.1 j)
        hsourceWhite (by rw [← hqeq, hqnorm])
      change 0 ≤ hexAWDepth
          (hlhc_prefixCoord (hlhda_augmentSide d internal) hraw.1 j) ∧
        hexAWDepth
          (hlhc_prefixCoord (hlhda_augmentSide d internal) hraw.1 j) ≤
            M + 1
      rw [hgeom.2, hsourceDepth]
      omega

theorem hlhda_depth_congr {xs ys : List ℤ} (hxy : xs = ys)
    {hx : (ofTurns hexAWStart 1 xs).IsLegalSAW}
    {hy : (ofTurns hexAWStart 1 ys).IsLegalSAW} (k : ℕ) :
    hlhd_depth xs hx k = hlhd_depth ys hy k := by
  subst ys
  have hp : hx = hy := Subsingleton.elim _ _
  subst hy
  rfl

theorem hlhda_prefixAugment_depth_bounds
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    ∀ j, j ≤ (hlhda_prefixAugment ts hleg).length →
      0 ≤ hlhd_depth (hlhda_prefixAugment ts hleg)
          (hlhda_prefixAugment_isLegalSAW ts hleg) j ∧
        hlhd_depth (hlhda_prefixAugment ts hleg)
          (hlhda_prefixAugment_isLegalSAW ts hleg) j ≤ M + 1 := by
  have hne : ts ≠ [] := by
    intro hnil
    subst ts
    have hcp : hlhda_cutPos [] hleg = 0 := by
      exact Nat.eq_zero_of_le_zero (hlhda_cutPos_le [] hleg)
    rw [hcp, hlhda_depth_zero] at hcut
    omega
  have htakeNe : ts.take (hlhda_cutPos ts hleg) ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    rw [List.length_take_of_le (hlhda_cutPos_le ts hleg)] at hlen
    simp only [List.length_nil] at hlen
    have hpos := hlhda_cutPos_pos hleg hne
    omega
  obtain ⟨t, us, hpre⟩ := List.exists_cons_of_ne_nil htakeNe
  let d := (hlhda_cutState ts hleg).dir
  obtain ⟨hd, hlegal, hnodup, hscore, hflat⟩ :=
    hlhda_prefix_side_hypotheses hleg hne hpre
  let haug := hlhda_augmentSide_isLegalSAW d (loopReverse us)
    hd hlegal hnodup hscore hflat
  have hrawEq : hlhda_prefixAugment ts hleg =
      hlhda_augmentSide d (loopReverse us) := by
    unfold hlhda_prefixAugment
    split <;> simp_all [d]
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  let source := hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg)
  have hsourceWhite : source.color = .white := by
    simpa [source] using hcutWhite
  have hsourceDepth : hexAWDepth source = M := by
    simpa [source, hlhd_depth] using hcut
  have hnorm : ∀ q ∈
      hlha_edgeVertices HexReturnCoord.zero d (loopReverse us),
      ∃ c : HexAWCoord,
        0 ≤ hexAWDepth c ∧ hexAWDepth c ≤ M ∧
          q = (hexAWReturnPos source).add
            (hlha_negCoord (hexAWReturnPos c)) := by
    intro q hq
    obtain ⟨k, hk, hqeq⟩ :=
      hlhda_prefix_normalized_point hleg hpre hq
    let c := hlhc_prefixCoord ts hleg.1 k
    refine ⟨c, ?_, ?_, ?_⟩
    · exact hnonneg k (le_trans hk (hlhda_cutPos_le ts hleg))
    · have hmax := hlhda_cutPos_max ts hleg k
          (le_trans hk (hlhda_cutPos_le ts hleg))
      rw [hcut] at hmax
      exact hmax
    · simpa [source, c] using hqeq
  have hb := hlhda_augmentSide_depth_bounds d (loopReverse us) hd haug
    source hsourceWhite M hsourceDepth hnorm
  intro j hj
  have hj' : j ≤ (hlhda_augmentSide d (loopReverse us)).length := by
    simpa [hrawEq] using hj
  have hbj := hb j hj'
  constructor
  · rw [hlhda_depth_congr hrawEq j]
    exact hbj.1
  · rw [hlhda_depth_congr hrawEq j]
    exact hbj.2

theorem hlhda_suffix_initial_notFlat
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ))
    {t : ℤ} {us : List ℤ}
    (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us) :
    hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) ≠
      hlhda_flatNeighbor := by
  let cp := hlhda_cutPos ts hleg
  let r := hlhda_cutState ts hleg
  let d0 := r.dir.turn t
  let d := hlha_negCoord d0
  have hne : ts ≠ [] := by
    intro hnil
    subst ts
    have hcp : hlhda_cutPos [] hleg = 0 := by
      exact Nat.eq_zero_of_le_zero (hlhda_cutPos_le [] hleg)
    rw [hcp, hlhda_depth_zero] at hcut
    omega
  intro hflat
  have hdmem : hlhda_flatNeighbor ∈
      hlha_edgeVertices HexReturnCoord.zero d us := by
    rw [← hflat]
    exact hlhda_firstDir_mem_edgeVertices d us
  have husNil := hlhda_suffix_flat_forces_terminal hleg hne hsuf hdmem
  subst us
  have hsufLen := congrArg List.length hsuf
  simp only [List.length_drop, List.length_cons, List.length_nil] at hsufLen
  have hcple := hlhda_cutPos_le ts hleg
  have hlast : cp + 1 = ts.length := by omega
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  change (hlhc_prefixCoord ts hleg.1 cp).color = .white at hcutWhite
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
  have hnormalized :
      (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 cp)).add
          (hlha_negCoord
            (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (cp + 1)))) =
        hlhda_flatNeighbor := by
    rw [← hdCoord]
    exact hflat
  have hnextCoord : hlhc_prefixCoord ts hleg.1 (cp + 1) =
      hexAWNeighbor (hlhc_prefixCoord ts hleg.1 cp) 0 :=
    (hlhda_normalized_eq_flat_iff
      (hlhc_prefixCoord ts hleg.1 cp)
      (hlhc_prefixCoord ts hleg.1 (cp + 1)) hcutWhite).mp hnormalized
  have hnextDepth : hlhd_depth ts hleg (cp + 1) =
      hlhd_depth ts hleg cp := by
    unfold hlhd_depth
    rw [hnextCoord, hlhda_depth_neighbor_zero]
  rw [hlast, hend, hcut] at hnextDepth
  omega

theorem hlhda_suffixAugment_depth_bounds
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    ∀ j, j ≤ (hlhda_suffixAugment ts hleg).length →
      0 ≤ hlhd_depth (hlhda_suffixAugment ts hleg)
          (hlhda_suffixAugment_isLegalSAW ts hleg) j ∧
        hlhd_depth (hlhda_suffixAugment ts hleg)
          (hlhda_suffixAugment_isLegalSAW ts hleg) j ≤ M + 1 := by
  have hne : ts ≠ [] := by
    intro hnil
    subst ts
    have hcp : hlhda_cutPos [] hleg = 0 := by
      exact Nat.eq_zero_of_le_zero (hlhda_cutPos_le [] hleg)
    rw [hcp, hlhda_depth_zero] at hcut
    omega
  have hcplt : hlhda_cutPos ts hleg < ts.length := by
    have hcple := hlhda_cutPos_le ts hleg
    by_contra hlt
    have hcpEq : hlhda_cutPos ts hleg = ts.length := by omega
    rw [hcpEq, hend] at hcut
    omega
  have hdropNe : ts.drop (hlhda_cutPos ts hleg) ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_drop, List.length_nil] at hlen
    omega
  obtain ⟨t, us, hsuf⟩ := List.exists_cons_of_ne_nil hdropNe
  let d := hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)
  have hnotFlat := hlhda_suffix_initial_notFlat hleg M hM hend hcut hsuf
  obtain ⟨hd, hlegal, hnodup, hscore, hflat⟩ :=
    hlhda_suffix_side_hypotheses hleg hsuf hnotFlat
  let haug := hlhda_augmentSide_isLegalSAW d us
    hd hlegal hnodup hscore hflat
  have hrawEq : hlhda_suffixAugment ts hleg =
      hlhda_augmentSide d us := by
    unfold hlhda_suffixAugment
    split <;> simp_all [d]
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  let source := hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg)
  have hsourceWhite : source.color = .white := by
    simpa [source] using hcutWhite
  have hsourceDepth : hexAWDepth source = M := by
    simpa [source, hlhd_depth] using hcut
  have hnorm : ∀ q ∈
      hlha_edgeVertices HexReturnCoord.zero d us,
      ∃ c : HexAWCoord,
        0 ≤ hexAWDepth c ∧ hexAWDepth c ≤ M ∧
          q = (hexAWReturnPos source).add
            (hlha_negCoord (hexAWReturnPos c)) := by
    intro q hq
    obtain ⟨k, hk, hqeq⟩ :=
      hlhda_suffix_normalized_point hleg hsuf hq
    let c := hlhc_prefixCoord ts hleg.1 k
    refine ⟨c, ?_, ?_, ?_⟩
    · exact hnonneg k hk
    · have hmax := hlhda_cutPos_max ts hleg k hk
      rw [hcut] at hmax
      exact hmax
    · simpa [source, c] using hqeq
  have hb := hlhda_augmentSide_depth_bounds d us hd haug
    source hsourceWhite M hsourceDepth hnorm
  intro j hj
  have hj' : j ≤ (hlhda_augmentSide d us).length := by
    simpa [hrawEq] using hj
  have hbj := hb j hj'
  constructor
  · rw [hlhda_depth_congr hrawEq j]
    exact hbj.1
  · rw [hlhda_depth_congr hrawEq j]
    exact hbj.2

theorem hlhda_prefixAugment_final_returnPos
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hne : ts ≠ []) :
    hexAWReturnPos
        (hlhc_prefixCoord (hlhda_prefixAugment ts hleg)
          (hlhda_prefixAugment_isLegalSAW ts hleg).1
          (hlhda_prefixAugment ts hleg).length) =
      hlhda_spacerRoot.add
        (hexAWReturnPos
          (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))) := by
  have htakeNe : ts.take (hlhda_cutPos ts hleg) ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    rw [List.length_take_of_le (hlhda_cutPos_le ts hleg)] at hlen
    simp only [List.length_nil] at hlen
    have hpos := hlhda_cutPos_pos hleg hne
    omega
  obtain ⟨t, us, hpre⟩ := List.exists_cons_of_ne_nil htakeNe
  let r := hlhda_cutState ts hleg
  let d0 := HexReturnCoord.base.turn t
  let d := r.dir
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
  have hnegFinal :
      (hlhr_coordRun (hlha_negCoord r.dir) (hlha_negCoord r.dir)
        (loopReverse us)).pos = hlha_negCoord r.pos := by
    have habs := congrArg HLHRCoordRun.pos hrev.2
    have htranslate := hlhda_coordRun_translate_pos r.pos
      (hlha_negCoord r.dir) (hlha_negCoord r.dir) (loopReverse us)
    rw [htranslate] at habs
    apply hlha_add_left_injective r.pos
    rw [habs, hlha_add_neg_self]
  have hrelFinal :
      (hlhr_coordRun r.dir r.dir (loopReverse us)).pos = r.pos := by
    have hneg := hlhda_coordRun_neg_pos
      (hlha_negCoord r.dir) (hlha_negCoord r.dir)
      (loopReverse us) hrevLegal
    simp only [hlha_negCoord_negCoord] at hneg
    rw [hneg, hnegFinal]
    exact hlha_negCoord_negCoord r.pos
  obtain ⟨hd, hlegal, hnodup, hscore, hflat⟩ :=
    hlhda_prefix_side_hypotheses hleg hne hpre
  have hrawEq : hlhda_prefixAugment ts hleg =
      hlhda_augmentSide d (loopReverse us) := by
    unfold hlhda_prefixAugment
    split <;> simp_all [d, r]
  have hrun := hlhda_prefixCoord_returnPos
    (hlhda_prefixAugment ts hleg)
    (hlhda_prefixAugment_isLegalSAW ts hleg)
    (hlhda_prefixAugment ts hleg).length
  rw [List.take_length] at hrun
  have hrPos := hlhda_prefixCoord_returnPos ts hleg
    (hlhda_cutPos ts hleg)
  change r.pos = _ at hrPos
  have hrunGeom :
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (hlhda_prefixAugment ts hleg)).pos =
        hlhda_spacerRoot.add
          (hexAWReturnPos
            (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))) := by
    rw [hrawEq, hlhda_coordRun_augmentSide_pos d (loopReverse us) hd]
    dsimp only [d]
    rw [hlha_zero_add, hrelFinal, hrPos]
  exact hrun.symm.trans hrunGeom

theorem hlhda_prefixAugment_final_color_depth
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    let raw := hlhda_prefixAugment ts hleg
    let hraw := hlhda_prefixAugment_isLegalSAW ts hleg
    (hlhc_prefixCoord raw hraw.1 raw.length).color = .white ∧
      hlhd_depth raw hraw raw.length = M + 1 := by
  dsimp only
  have hne : ts ≠ [] := by
    intro hnil
    subst ts
    have hcp : hlhda_cutPos [] hleg = 0 := by
      exact Nat.eq_zero_of_le_zero (hlhda_cutPos_le [] hleg)
    rw [hcp, hlhda_depth_zero] at hcut
    omega
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  let source := hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg)
  let out := hlhc_prefixCoord (hlhda_prefixAugment ts hleg)
    (hlhda_prefixAugment_isLegalSAW ts hleg).1
    (hlhda_prefixAugment ts hleg).length
  have hpos := hlhda_prefixAugment_final_returnPos hleg hne
  have hgeom := hlhda_spacer_normalized_depth_color source
    hexAWOriginCoord out (by simpa [source] using hcutWhite) (by
      simpa [source, out, hexAWOriginCoord, hexAWReturnPos,
        HexReturnCoord.zero, HexReturnCoord.add, hlha_negCoord] using hpos)
  have hsourceDepth : hexAWDepth source = M := by
    simpa [source, hlhd_depth] using hcut
  have horiginDepth : hexAWDepth hexAWOriginCoord = 0 := by
    rfl
  constructor
  · simpa [out, hexAWOriginCoord, hlhd_swapColor] using hgeom.1
  · change hexAWDepth out = M + 1
    rw [hgeom.2, hsourceDepth, horiginDepth]
    omega

theorem hlhda_suffixAugment_final_returnPos
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    hexAWReturnPos
        (hlhc_prefixCoord (hlhda_suffixAugment ts hleg)
          (hlhda_suffixAugment_isLegalSAW ts hleg).1
          (hlhda_suffixAugment ts hleg).length) =
      hlhda_spacerRoot.add
        ((hexAWReturnPos
          (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add
        (hlha_negCoord
          (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 ts.length)))) := by
  have hcplt : hlhda_cutPos ts hleg < ts.length := by
    have hcple := hlhda_cutPos_le ts hleg
    by_contra hlt
    have hcpEq : hlhda_cutPos ts hleg = ts.length := by omega
    rw [hcpEq, hend] at hcut
    omega
  have hdropNe : ts.drop (hlhda_cutPos ts hleg) ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_drop, List.length_nil] at hlen
    omega
  obtain ⟨t, us, hsuf⟩ := List.exists_cons_of_ne_nil hdropNe
  let r := hlhda_cutState ts hleg
  let d0 := r.dir.turn t
  let d := hlha_negCoord d0
  have hus : ∀ u ∈ us, u = 1 ∨ u = -1 := by
    intro u hu
    have hudrop : u ∈ ts.drop (hlhda_cutPos ts hleg) := by
      rw [hsuf]
      simp [hu]
    exact hleg.1 u (List.mem_of_mem_drop hudrop)
  have hnotFlat := hlhda_suffix_initial_notFlat hleg M hM hend hcut hsuf
  obtain ⟨hd, hlegal, hnodup, hscore, hflat⟩ :=
    hlhda_suffix_side_hypotheses hleg hsuf hnotFlat
  have hrawEq : hlhda_suffixAugment ts hleg =
      hlhda_augmentSide d us := by
    unfold hlhda_suffixAugment
    split <;> simp_all [d, d0, r]
  have hfull : hlhr_coordRun (r.pos.add d0) d0 us =
      hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts := by
    calc
      hlhr_coordRun (r.pos.add d0) d0 us =
          hlhr_coordRun r.pos r.dir (t :: us) := by
            simp only [hlhr_coordRun, d0]
      _ = hlhr_coordRun r.pos r.dir
          (ts.drop (hlhda_cutPos ts hleg)) := by rw [hsuf]
      _ = hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
          (ts.take (hlhda_cutPos ts hleg) ++
            ts.drop (hlhda_cutPos ts hleg)) := by
            rw [hlha_coordRun_append]
            rfl
      _ = hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts := by
            rw [List.take_append_drop]
  have hfullPos := congrArg HLHRCoordRun.pos hfull
  rw [hlhda_coordRun_translate_pos r.pos d0 d0 us] at hfullPos
  have hrPos := hlhda_prefixCoord_returnPos ts hleg
    (hlhda_cutPos ts hleg)
  change r.pos =
    hexAWReturnPos
      (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg)) at hrPos
  have hendPos := hlhda_prefixCoord_returnPos ts hleg ts.length
  rw [List.take_length] at hendPos
  have hrelForward : (hlhr_coordRun d0 d0 us).pos =
      (hlha_negCoord r.pos).add
        (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 ts.length)) := by
    rw [hendPos] at hfullPos
    apply hlha_add_left_injective r.pos
    rw [hfullPos, hlhda_add_neg_left]
  have hrelNeg := hlhda_coordRun_neg_pos d0 d0 us hus
  change (hlhr_coordRun d d us).pos =
    hlha_negCoord (hlhr_coordRun d0 d0 us).pos at hrelNeg
  have hrelFinal : (hlhr_coordRun d d us).pos =
      r.pos.add
        (hlha_negCoord
          (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 ts.length))) := by
    rw [hrelNeg, hrelForward]
    rcases r.pos with ⟨rx, ry⟩
    rcases hexAWReturnPos (hlhc_prefixCoord ts hleg.1 ts.length) with
      ⟨ex, ey⟩
    simp [HexReturnCoord.add, hlha_negCoord, add_comm]
  have hrun := hlhda_prefixCoord_returnPos
    (hlhda_suffixAugment ts hleg)
    (hlhda_suffixAugment_isLegalSAW ts hleg)
    (hlhda_suffixAugment ts hleg).length
  rw [List.take_length] at hrun
  have hrunGeom :
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (hlhda_suffixAugment ts hleg)).pos =
        hlhda_spacerRoot.add
          ((hexAWReturnPos
            (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add
          (hlha_negCoord
            (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 ts.length)))) := by
    rw [hrawEq, hlhda_coordRun_augmentSide_pos d us hd]
    rw [hlha_zero_add, hrelFinal, hrPos]
  exact hrun.symm.trans hrunGeom

theorem hlhda_suffixAugment_final_color_depth
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    let raw := hlhda_suffixAugment ts hleg
    let hraw := hlhda_suffixAugment_isLegalSAW ts hleg
    (hlhc_prefixCoord raw hraw.1 raw.length).color = .black ∧
      hlhd_depth raw hraw raw.length = M + 1 := by
  dsimp only
  have hne : ts ≠ [] := by
    intro hnil
    subst ts
    have hcp : hlhda_cutPos [] hleg = 0 := by
      exact Nat.eq_zero_of_le_zero (hlhda_cutPos_le [] hleg)
    rw [hcp, hlhda_depth_zero] at hcut
    omega
  have hcutWhite := (hlhda_cut_local hleg hne).2.1
  let source := hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg)
  let terminal := hlhc_prefixCoord ts hleg.1 ts.length
  let out := hlhc_prefixCoord (hlhda_suffixAugment ts hleg)
    (hlhda_suffixAugment_isLegalSAW ts hleg).1
    (hlhda_suffixAugment ts hleg).length
  have hpos := hlhda_suffixAugment_final_returnPos hleg M hM hend hcut
  have hgeom := hlhda_spacer_normalized_depth_color source terminal out
    (by simpa [source] using hcutWhite) (by
      simpa [source, terminal, out] using hpos)
  have hsourceDepth : hexAWDepth source = M := by
    simpa [source, hlhd_depth] using hcut
  have hterminalDepth : hexAWDepth terminal = 0 := by
    simpa [terminal, hlhd_depth] using hend
  constructor
  · have hswap : hlhd_swapColor terminal.color = .black := by
      rw [hendWhite]
      rfl
    exact hgeom.1.trans hswap
  · change hexAWDepth out = M + 1
    rw [hgeom.2, hsourceDepth, hterminalDepth]
    omega

theorem hlhda_prefixTerminalEdge_inward
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    let raw := hlhda_prefixAugment ts hleg
    let hraw := hlhda_prefixAugment_isLegalSAW ts hleg
    let e := hlhda_terminalEdge raw hraw (hlhda_prefixAugment_ne ts hleg)
    e = 1 ∨ e = 2 := by
  dsimp only
  let raw := hlhda_prefixAugment ts hleg
  let hraw := hlhda_prefixAugment_isLegalSAW ts hleg
  let e := hlhda_terminalEdge raw hraw (hlhda_prefixAugment_ne ts hleg)
  let prev := hlhc_prefixCoord raw hraw.1 (raw.length - 1)
  let far := hlhc_prefixCoord raw hraw.1 raw.length
  have hfar := hlhda_prefixAugment_final_color_depth hleg M hM hcut
  have hspec := hlhda_terminalEdge_spec raw hraw
    (hlhda_prefixAugment_ne ts hleg)
  change hexAWNeighbor prev e = far at hspec
  have hene : e ≠ 0 := by
    intro he0
    have hprevBlack : prev.color = .black := by
      cases hc : prev.color with
      | black => rfl
      | white =>
          have hnextBlack := hlhda_neighbor_color_white hc hspec
          rw [hfar.1] at hnextBlack
          contradiction
    have hbounds := hlhda_prefixAugment_depth_bounds hleg M hM
      hnonneg hcut
    have hprevLt := hlhda_physical_black_depth_lt raw hraw (M + 1)
      (by omega) hbounds
      (k := raw.length - 1)
      (Nat.sub_lt (List.length_pos_iff.mpr
        (hlhda_prefixAugment_ne ts hleg)) (by omega)) hprevBlack
    have hdepthEq := congrArg hexAWDepth hspec
    rw [he0, hlhda_depth_neighbor_zero] at hdepthEq
    change hexAWDepth prev < M + 1 at hprevLt
    have hfarDepth := hfar.2
    change hexAWDepth far = M + 1 at hfarDepth
    omega
  exact hlhd_fin3_inward_of_ne_zero e hene

theorem hlhda_completedPrefix_endpointIsLegalSAW
    (ts : List ℤ) (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1
      (hlhda_completedPrefix ts hleg)).EndpointIsLegalSAW := by
  unfold hlhda_completedPrefix
  apply (endpointIsLegalSAW_append_one_iff _ _ _ _).2
  exact ⟨hlhda_prefixAugment_isLegalSAW ts hleg,
    hlhd_exitTurn_legal _⟩

theorem hlhda_completedPrefix_endsAt
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    let raw := hlhda_prefixAugment ts hleg
    let hraw := hlhda_prefixAugment_isLegalSAW ts hleg
    let far := hlhc_prefixCoord raw hraw.1 raw.length
    (ofTurns hexAWStart 1 (hlhda_completedPrefix ts hleg)).EndsAt
      (hexAWMid far 0) := by
  dsimp only
  let raw := hlhda_prefixAugment ts hleg
  let hraw := hlhda_prefixAugment_isLegalSAW ts hleg
  let e := hlhda_terminalEdge raw hraw (hlhda_prefixAugment_ne ts hleg)
  let prev := hlhc_prefixCoord raw hraw.1 (raw.length - 1)
  let far := hlhc_prefixCoord raw hraw.1 raw.length
  have hspec := hlhda_terminalEdge_spec raw hraw
    (hlhda_prefixAugment_ne ts hleg)
  change hexAWNeighbor prev e = far at hspec
  have hin := hlhda_prefixTerminalEdge_inward hleg M hM hnonneg hcut
  have hfar := (hlhda_prefixAugment_final_color_depth hleg M hM hcut).1
  have hend := hlhd_endsAt_lastPrefixEdge raw hraw
    (hlhda_prefixAugment_ne ts hleg) e hspec
  have hk : raw.length - 1 < raw.length :=
    Nat.sub_lt (List.length_pos_iff.mpr
      (hlhda_prefixAugment_ne ts hleg)) (by omega)
  have hsucc : raw.length - 1 + 1 = raw.length := by omega
  have hspec' :
      hexAWNeighbor (hlhc_prefixCoord raw hraw.1 (raw.length - 1)) e =
        hlhc_prefixCoord raw hraw.1 (raw.length - 1 + 1) := by
    simpa only [hsucc] using hspec
  have hhead := hlhd_prefix_edge_unit raw hraw
    (raw.length - 1) hk e hspec'
  rw [hsucc, List.take_length] at hhead
  have hout := hlhd_append_exit_endsAt raw prev far e hend hhead
    hspec hfar hin
  simpa [hlhda_completedPrefix, raw, hraw, e, prev, far] using hout

theorem hlhda_completedPrefix_horizontal
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    ∀ k, k < (hlhda_completedPrefix ts hleg).length →
      0 ≤ hexAWBookRe2
          (hlhc_prefixCoord (hlhda_completedPrefix ts hleg)
            (hlhda_completedPrefix_endpointIsLegalSAW ts hleg).1 k) ∧
        hexAWBookRe2
          (hlhc_prefixCoord (hlhda_completedPrefix ts hleg)
            (hlhda_completedPrefix_endpointIsLegalSAW ts hleg).1 k) ≤
          3 * (M + 1) := by
  let raw := hlhda_prefixAugment ts hleg
  let hraw := hlhda_prefixAugment_isLegalSAW ts hleg
  let e := hlhda_terminalEdge raw hraw (hlhda_prefixAugment_ne ts hleg)
  have hout : hlhda_completedPrefix ts hleg =
      raw ++ [hlhd_exitTurn e] := rfl
  have hbounds := hlhda_prefixAugment_depth_bounds hleg M hM hnonneg hcut
  have hfar := hlhda_prefixAugment_final_color_depth hleg M hM hcut
  change
    (hlhc_prefixCoord raw hraw.1 raw.length).color = .white ∧
      hexAWDepth (hlhc_prefixCoord raw hraw.1 raw.length) = M + 1 at hfar
  intro k hk
  rw [hout] at hk
  have hkle : k ≤ raw.length := by
    simp only [List.length_append, List.length_singleton] at hk
    omega
  have hcoord :
      hlhc_prefixCoord (hlhda_completedPrefix ts hleg)
          (hlhda_completedPrefix_endpointIsLegalSAW ts hleg).1 k =
        hlhc_prefixCoord raw hraw.1 k := by
    apply hlhda_prefixCoord_eq_of_take_eq
    rw [hout, List.take_append_of_le_length hkle]
  rw [hcoord]
  rcases lt_or_eq_of_le hkle with hklt | rfl
  · exact hlhda_physical_book_bounds raw hraw (M + 1)
      (by omega) hbounds hklt
  · have hbook :
        hexAWBookRe2 (hlhc_prefixCoord raw hraw.1 raw.length) =
          3 * (M + 1) - 1 := by
      rw [hexAWBookRe2, hfar.1]
      change 3 * hexAWDepth (hlhc_prefixCoord raw hraw.1 raw.length) - 1 =
        3 * (M + 1) - 1
      have hfarDepth := hfar.2
      change hexAWDepth (hlhc_prefixCoord raw hraw.1 raw.length) = M + 1
        at hfarDepth
      rw [hfarDepth]
    rw [hbook]
    have hfarDepth := hfar.2
    change hexAWDepth (hlhc_prefixCoord raw hraw.1 raw.length) = M + 1
      at hfarDepth
    omega

end
end StatMech.Universality
