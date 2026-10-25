/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part6


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_completedPrefix_mem_topAtWidth
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    HexCSTopWalkAtWidth (M + 1) (by omega)
      (hlhda_completedPrefix ts hleg) := by
  exact (hlhda_completedPrefixColumnWalk hleg M hM hnonneg hcut).mem_topAtWidth
    (by omega)

theorem hlhda_prefixCoord_returnPos_legal (ws : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ws).LegalTurns) (k : ℕ) :
    (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (ws.take k)).pos =
      hexAWReturnPos (hlhc_prefixCoord ws hlegal k) := by
  rw [hlhda_coordRuns_pos_eq]
  exact hexEndpointCoordRun_pos_eq_aw (ws.take k)
    (hlhc_prefixCoord ws hlegal k)
    (by
      intro t ht
      exact hlegal t (List.mem_of_mem_take ht))
    (hlhc_prefixCoord_vertex ws hlegal k)

theorem hlhda_prefix_edge_unit_legal (ws : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ws).LegalTurns)
    (k : ℕ) (hk : k < ws.length) (e : Fin 3)
    (he : hexAWNeighbor (hlhc_prefixCoord ws hlegal k) e =
      hlhc_prefixCoord ws hlegal (k + 1)) :
    hexUnit (hexInfra_headAccum 1 (ws.take (k + 1))) =
      hexUnit (hexAWHeading (hlhc_prefixCoord ws hlegal k) e) := by
  have hstep :
      hexJordan_vertexPos hexAWStart 1 ws (k + 1) -
          hexJordan_vertexPos hexAWStart 1 ws k =
        hexUnit (hexInfra_headAccum 1 (ws.take (k + 1))) := by
    rw [hexEndpoint_vertexPos_eq_nextMid_sub ws k hk]
    unfold hexJordan_vertexPos halfStep
    ring
  have hkpos : hexJordan_vertexPos hexAWStart 1 ws k =
      hexAWPos (hlhc_prefixCoord ws hlegal k) := by
    simpa only [hexJordan_vertexPos] using
      hlhc_prefixCoord_vertex ws hlegal k
  have hsuccpos : hexJordan_vertexPos hexAWStart 1 ws (k + 1) =
      hexAWPos (hlhc_prefixCoord ws hlegal (k + 1)) := by
    simpa only [hexJordan_vertexPos] using
      hlhc_prefixCoord_vertex ws hlegal (k + 1)
  rw [hkpos, hsuccpos] at hstep
  have hcoord :
      hexAWPos (hlhc_prefixCoord ws hlegal (k + 1)) -
          hexAWPos (hlhc_prefixCoord ws hlegal k) =
        hexUnit (hexAWHeading (hlhc_prefixCoord ws hlegal k) e) := by
    rw [← he]
    exact hexAWPos_neighbor _ _
  exact hstep.symm.trans hcoord

theorem hlhda_coordVertices_append_single (p d : HexReturnCoord)
    (ws : List ℤ) (t : ℤ) :
    hlha_coordVertices p d (ws ++ [t]) =
      hlha_coordVertices p d ws ++
        [(hlhr_coordRun p d ws).pos.add
          ((hlhr_coordRun p d ws).dir.turn t)] := by
  induction ws generalizing p d with
  | nil => simp [hlha_coordVertices, hlhr_coordRun]
  | cons u ws ih =>
      simp only [List.cons_append, hlha_coordVertices, hlhr_coordRun,
        List.cons_append]
      exact congrArg (List.cons p)
        (ih (p.add (d.turn u)) (d.turn u))

theorem hlhda_suffixTerminalEdge_zero
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    let raw := hlhda_suffixAugment ts hleg
    let hraw := hlhda_suffixAugment_isLegalSAW ts hleg
    hlhda_terminalEdge raw hraw (hlhda_suffixAugment_ne ts hleg) = 0 := by
  dsimp only
  let raw := hlhda_suffixAugment ts hleg
  let hraw := hlhda_suffixAugment_isLegalSAW ts hleg
  let e := hlhda_terminalEdge raw hraw (hlhda_suffixAugment_ne ts hleg)
  let prev := hlhc_prefixCoord raw hraw.1 (raw.length - 1)
  let far := hlhc_prefixCoord raw hraw.1 raw.length
  have hspec := hlhda_terminalEdge_spec raw hraw
    (hlhda_suffixAugment_ne ts hleg)
  change hexAWNeighbor prev e = far at hspec
  have hfar := hlhda_suffixAugment_final_color_depth hleg M hM
    hend hendWhite hcut
  have hbounds := hlhda_suffixAugment_depth_bounds hleg M hM
    hnonneg hend hcut
  apply hlhd_neighbor_black_max_edge_zero prev far e hspec hfar.1
  have hidx : raw.length - 1 ≤
      (hlhda_suffixAugment ts hleg).length := by
    simp only [raw]
    omega
  have hprev := (hbounds (raw.length - 1) hidx).2
  change hexAWDepth prev ≤ M + 1 at hprev
  have hfarDepth := hfar.2
  change hexAWDepth far = M + 1 at hfarDepth
  omega


theorem hlhda_suffixAugment_terminal_top
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    let raw := hlhda_suffixAugment ts hleg
    let hraw := hlhda_suffixAugment_isLegalSAW ts hleg
    let top := hlhc_prefixCoord raw hraw.1 (raw.length - 1)
    top.color = .white ∧
      hexAWDepth top = M + 1 ∧
      (ofTurns hexAWStart 1 raw).EndsAt (hexAWMid top 0) := by
  dsimp only
  let raw := hlhda_suffixAugment ts hleg
  let hraw := hlhda_suffixAugment_isLegalSAW ts hleg
  let top := hlhc_prefixCoord raw hraw.1 (raw.length - 1)
  let far := hlhc_prefixCoord raw hraw.1 raw.length
  have he0 := hlhda_suffixTerminalEdge_zero hleg M hM hnonneg
    hend hendWhite hcut
  have hlast := hlhda_terminalEdge_spec raw hraw
    (hlhda_suffixAugment_ne ts hleg)
  rw [he0] at hlast
  change hexAWNeighbor top 0 = far at hlast
  have hfar := hlhda_suffixAugment_final_color_depth hleg M hM
    hend hendWhite hcut
  change far.color = .black ∧ hexAWDepth far = M + 1 at hfar
  have htopWhite : top.color = .white := by
    cases hc : top.color with
    | white => rfl
    | black =>
        have hfarWhite := hlhda_neighbor_color_black hc hlast
        rw [hfar.1] at hfarWhite
        contradiction
  have htopDepth : hexAWDepth top = M + 1 := by
    have hd := congrArg hexAWDepth hlast
    rw [hlhda_depth_neighbor_zero, hfar.2] at hd
    exact hd
  refine ⟨htopWhite, htopDepth, ?_⟩
  exact hlhd_endsAt_lastPrefixEdge raw hraw
    (hlhda_suffixAugment_ne ts hleg) 0 hlast

end
end StatMech.Universality
