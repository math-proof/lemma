/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCyclicAtomSupport
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointPieceRigidity
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointTripletOrbit
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripStartReturn
import Structure.StatisticalMechanics.Code.Universality.HexCorrectedStripLocal


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCS_support_endsAt_edge
    (R : HexFiniteRegion) (c : HexAWCoord) (ts : List ℤ)
    (hsupport : endpointCombinedSummand R.inRegion hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts ≠ 0) :
    ∃ e : Fin 3, (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c e) := by
  have hends := R.endpointCombined_support_endsAt hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts hsupport
  rcases hends with hp | hq | hr
  · refine ⟨0, ?_⟩
    rw [← hexAW_labelMid_eq_mid c 0]
    simpa [labelMid] using hp
  · refine ⟨1, ?_⟩
    rw [← hexAW_labelMid_eq_mid c 1]
    simpa [labelMid] using hq
  · refine ⟨2, ?_⟩
    rw [← hexAW_labelMid_eq_mid c 2]
    simpa [labelMid] using hr

theorem hexCS_terminalPairCertificate_exists
    {T L : ℕ} {hT : 0 < T}
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L)
    (ts : List ℤ)
    (hts : ts ∈ (hexCSFiniteRegion T L hT).endpointVisitClassFinset
      hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 3) :
    ∃ D : HexCSTerminalPairCertificate T L hT c,
      ts ∈ D.pair.piece := by
  let R := hexCSFiniteRegion T L hT
  have hs := (R.mem_endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 3 ts).mp hts
  have hvalid := R.endpointCombined_support_valid hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts hs.1
  obtain ⟨endEdge, hend⟩ := hexCS_support_endsAt_edge R c ts hs.1
  have hnotOutside := hexCS_vertex_ne_outside_start c hc
  obtain ⟨C⟩ := hexEndpoint_local_crossing_of_count_three
    ts c endEdge hnotOutside hvalid.1 hend hs.2
  obtain ⟨P, hmem, hstem, hcount⟩ :=
    hexCS_cyclicLoopPair_of_terminal_with_stem
      c endEdge ts C hnotOutside ⟨hvalid.1, hvalid.2, hend⟩ hs.2
  exact ⟨⟨P, hstem, hcount⟩, hmem⟩


theorem hexCS_visitClass_three_sum_zero
    {T L : ℕ} {hT : 0 < T}
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) :
    ∑ ts ∈ (hexCSFiniteRegion T L hT).endpointVisitClassFinset
        hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 3,
      endpointCombinedSummand (hexCSFiniteRegion T L hT).inRegion
        hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0 := by
  classical
  let R := hexCSFiniteRegion T L hT
  let S := R.endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 3
  let piece : HexCSTerminalPairCertificate T L hT c → Finset (List ℤ) :=
    fun D => D.pair.piece
  have hdu : hexAWMid c 0 - hexAWPos c ≠ 0 :=
    hexAW_base_du_ne_zero c
  have hcover : ∀ ts ∈ S,
      ∃ D : HexCSTerminalPairCertificate T L hT c,
        ts ∈ piece D ∧ piece D ⊆ S := by
    intro ts hts
    obtain ⟨D, hmem⟩ := hexCS_terminalPairCertificate_exists c hc ts hts
    refine ⟨D, hmem, ?_⟩
    intro u hu
    have hus := D.pair.piece_subset_endpointCombinedSupportFinset hdu hu
    apply (R.mem_endpointVisitClassFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 3 u).2
    exact ⟨(R.mem_endpointCombinedSupportFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) u).mp hus,
        D.count u hu⟩
  have hoverlap : ∀ D E : HexCSTerminalPairCertificate T L hT c,
      ∀ z ∈ S, z ∈ piece D → z ∈ piece E →
        piece D = piece E := by
    intro D E z _ hzD hzE
    exact hexCS_cyclicPair_piece_eq_of_overlap hdu
      D.pair E.pair D.stem E.stem z hzD hzE
  obtain ⟨atoms, hatoms, hdisjoint⟩ :=
    finitePiecePartition_exists S piece hcover hoverlap
  change ∑ ts ∈ S,
    endpointCombinedSummand R.inRegion hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 0
  rw [← hatoms, Finset.sum_biUnion hdisjoint]
  exact Finset.sum_eq_zero fun D _ => D.pair.sum_piece_zero hdu


theorem hexCS_combinedSupport_sum_zero
    {T L : ℕ} {hT : 0 < T}
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) :
    ∑ ts ∈ (hexCSFiniteRegion T L hT).endpointCombinedSupportFinset
        hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c),
      endpointCombinedSummand (hexCSFiniteRegion T L hT).inRegion
        hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0 := by
  let R := hexCSFiniteRegion T L hT
  let S1 := R.endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1
  let S2 := R.endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2
  let S3 := R.endpointVisitClassFinset hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 3
  have hnotOutside := hexCS_vertex_ne_outside_start c hc
  have hall (e : Fin 3) : R.inRegion (hexAWMid c e) := by
    change hexAWMid c e ∈ hexCSMids T L
    rw [hexCSMids, Finset.mem_biUnion]
    refine ⟨⟨c, hc⟩, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e, Finset.mem_univ _, rfl⟩
  have hreturn : ∀ ws : List ℤ,
      (ofTurns hexAWStart 1 ws).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ws).StaysIn R.inRegion ∧
        (ofTurns hexAWStart 1 ws).EndsAt hexAWStart → ws = [] := by
    intro ws hws
    exact hexCS_endpoint_return_eq_nil T L hT ws hws
  have h12 : ∑ ts ∈ S1 ∪ S2,
      endpointCombinedSummand R.inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0 :=
    hexEndpoint_visitOneTwo_sum_zero_aw
      R c hnotOutside hall hreturn
  have h3 : ∑ ts ∈ S3,
      endpointCombinedSummand R.inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0 := by
    exact hexCS_visitClass_three_sum_zero c hc
  have hdisjoint : Disjoint (S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]
    intro ts hts hts3
    have hcount3 := (R.mem_endpointVisitClassFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 3 ts).mp hts3 |>.2
    rcases Finset.mem_union.mp hts with hts1 | hts2
    · have hcount1 := (R.mem_endpointVisitClassFinset hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ts).mp hts1 |>.2
      omega
    · have hcount2 := (R.mem_endpointVisitClassFinset hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2 ts).mp hts2 |>.2
      omega
  change ∑ ts ∈ R.endpointCombinedSupportFinset hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c),
    endpointCombinedSummand R.inRegion hexAWStart 1
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0
  rw [R.endpointSupportFinset_eq_visitClasses, Finset.sum_union hdisjoint,
    h12, h3, add_zero]


theorem hexCS_localRelation (T L : ℕ) (hT : 0 < T) :
    HexCSLocalRelation T L hT := by
  intro vtx
  let R := hexCSFiniteRegion T L hT
  let c := vtx.1
  let du := hexAWMid c 0 - hexAWPos c
  have hsum : ∑ ts ∈ R.endpointCombinedSupportFinset
        hexAWStart 1 (hexAWPos c) du,
      endpointCombinedSummand R.inRegion hexAWStart 1
        (hexAWPos c) du ts = 0 := by
    exact hexCS_combinedSupport_sum_zero c vtx.2
  have hvertex :
      ((hexAWPos c + du) - hexAWPos c) *
          endpointParafObservable R.inRegion hexAWStart 1
            (hexAWPos c + du) (5 / 8) hexChi +
        ((hexAWPos c + hexOmega * du) - hexAWPos c) *
          endpointParafObservable R.inRegion hexAWStart 1
            (hexAWPos c + hexOmega * du) (5 / 8) hexChi +
        ((hexAWPos c + hexOmega ^ 2 * du) - hexAWPos c) *
          endpointParafObservable R.inRegion hexAWStart 1
            (hexAWPos c + hexOmega ^ 2 * du) (5 / 8) hexChi = 0 := by
    rw [endpointVertexSum_eq_tsum_combined]
    rw [tsum_eq_sum (s := R.endpointCombinedSupportFinset
      hexAWStart 1 (hexAWPos c) du)]
    · exact hsum
    · intro ts hts
      by_contra hne
      exact hts ((R.mem_endpointCombinedSupportFinset
        hexAWStart 1 (hexAWPos c) du ts).2 hne)
  change ∑ j : Fin 3,
      (hexAWMid c j - hexAWPos c) *
        hexCSObservable T L hT (hexAWMid c j) = 0
  rw [Fin.sum_univ_three]
  rw [← hexAW_labelMid_eq_mid c 0,
    ← hexAW_labelMid_eq_mid c 1,
    ← hexAW_labelMid_eq_mid c 2]
  simpa [hexCSObservable, R, du, labelMid] using hvertex

end
end StatMech.Universality
