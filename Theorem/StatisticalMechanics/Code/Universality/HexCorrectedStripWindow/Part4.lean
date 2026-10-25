/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part4


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

@[simp] theorem hexCSCoordPath_length
    (c : HexAWCoord) (h : Fin 6) (ts : List ℤ) :
    (hexCSCoordPath c h ts).length = ts.length + 2 := by
  induction ts generalizing c h with
  | nil => rfl
  | cons t ts ih => simp [hexCSCoordPath, ih]


theorem hexCSCoordPath_brick
    (c : HexAWCoord) (h0 : ℤ) (ts : List ℤ)
    (hfit : HexCSHeadingFits c (hexCSHeadingFin h0))
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexCSCoordPath c (hexCSHeadingFin h0) ts).map
        (fun q => hexBrickPos q - hexBrickPos c) =
      ons_pathVertices (hexCSBrickDirections h0 ts) := by
  induction ts generalizing c h0 with
  | nil =>
      simp only [hexCSCoordPath, hexCSBrickDirections_nil,
        ons_pathVertices_cons, ons_pathVertices_nil, List.map_cons,
        List.map_singleton, sub_self]
      have hs := hexBrickPos_neighbor c
        (hexCSEdgeOfHeading c (hexCSHeadingFin h0))
      rw [hexCSEdgeOfHeading_mod c (hexCSHeadingFin h0) hfit] at hs
      simp only [List.cons.injEq, List.map_cons, List.map_nil,
        List.cons.injEq, and_true]
      exact ⟨trivial, by simpa using (sub_eq_iff_eq_add').2 hs⟩
  | cons t ts ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := hexCSEdgeOfHeading c (hexCSHeadingFin h0)
      let c' := hexAWNeighbor c e
      have hfit' : HexCSHeadingFits c'
          (hexCSHeadingFin (h0 + t)) := by
        rw [hexCSHeadingFin_turn h0 t ht]
        exact hexCSHeadingFits_step c (hexCSHeadingFin h0) t hfit ht
      have hi := ih c' (h0 + t) hfit' htail
      have hs := hexBrickPos_neighbor c e
      have hemod : hexAWHeadingMod c e = hexCSHeadingFin h0 :=
        hexCSEdgeOfHeading_mod c (hexCSHeadingFin h0) hfit
      rw [hemod] at hs
      change hexBrickPos c' = hexBrickPos c +
        StatMech.Onsager.BaseCase.stepOf
          (hexBrickDir (hexCSHeadingFin h0)) at hs
      simp only [hexCSCoordPath, hexCSBrickDirections_cons,
        ons_pathVertices_cons, List.map_cons, sub_self,
        List.cons.injEq, true_and]
      rw [← hexCSHeadingFin_turn h0 t ht]
      change List.map (fun q => hexBrickPos q - hexBrickPos c)
          (hexCSCoordPath c' (hexCSHeadingFin (h0 + t)) ts) = _
      rw [← hi]
      simp only [List.map_map, Function.comp_apply]
      apply List.map_congr_left
      intro q hq
      change hexBrickPos q - hexBrickPos c =
        StatMech.Onsager.BaseCase.stepOf
            (hexBrickDir (hexCSHeadingFin h0)) +
          (hexBrickPos q - hexBrickPos c')
      rw [hs]
      abel


theorem hexCSCoordPath_pos
    (c : HexAWCoord) (m : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hfit : HexCSHeadingFits c (hexCSHeadingFin h0))
    (hmid : m = hexAWMid c
      (hexCSEdgeOfHeading c (hexCSHeadingFin h0)))
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexCSCoordPath c (hexCSHeadingFin h0) ts).map hexAWPos =
      hexAWPos c :: verticesAux m h0 ts := by
  induction ts generalizing c m h0 with
  | nil =>
      simp only [hexCSCoordPath, List.map_cons, List.map_singleton,
        verticesAux]
      have hh := hexCSEdgeOfHeading_halfStep c h0 hfit
      have hnext : hexAWPos (hexAWNeighbor c
          (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) =
          m + halfStep h0 := by
        calc
          hexAWPos (hexAWNeighbor c
              (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) =
              hexAWMid c (hexCSEdgeOfHeading c
                (hexCSHeadingFin h0)) +
                halfStep (hexAWHeading c
                  (hexCSEdgeOfHeading c (hexCSHeadingFin h0))) :=
            hexAWNeighborPos_eq_mid_add c _
          _ = m + halfStep h0 := by rw [← hmid, ← hh]
      rw [hnext]
      rfl
  | cons t ts ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := hexCSEdgeOfHeading c (hexCSHeadingFin h0)
      let c' := hexAWNeighbor c e
      let m' := m + halfStep h0 + halfStep (h0 + t)
      have hfit' : HexCSHeadingFits c'
          (hexCSHeadingFin (h0 + t)) := by
        rw [hexCSHeadingFin_turn h0 t ht]
        exact hexCSHeadingFits_step c (hexCSHeadingFin h0) t hfit ht
      have hcur : m + halfStep h0 = hexAWPos c' := by
        have hh := hexCSEdgeOfHeading_halfStep c h0 hfit
        change m = hexAWMid c e at hmid
        calc
          m + halfStep h0 = hexAWMid c e +
              halfStep (hexAWHeading c e) := by rw [hmid, hh]
          _ = hexAWPos (hexAWNeighbor c e) :=
            (hexAWNeighborPos_eq_mid_add c e).symm
          _ = hexAWPos c' := rfl
      have hmid' : m' = hexAWMid c'
          (hexCSEdgeOfHeading c' (hexCSHeadingFin (h0 + t))) := by
        have hh := hexCSEdgeOfHeading_halfStep c' (h0 + t) hfit'
        have hm := hexAWMid_sub_pos_eq_halfStep c'
          (hexCSEdgeOfHeading c' (hexCSHeadingFin (h0 + t)))
        rw [← hh] at hm
        change m + halfStep h0 + halfStep (h0 + t) = _
        calc
          m + halfStep h0 + halfStep (h0 + t) =
              hexAWPos c' + halfStep (h0 + t) := by rw [hcur]
          _ = hexAWMid c' (hexCSEdgeOfHeading c'
              (hexCSHeadingFin (h0 + t))) := by
            exact ((sub_eq_iff_eq_add').1 hm).symm
      have hi := ih c' m' (h0 + t) hfit' hmid' htail
      simp only [hexCSCoordPath, List.map_cons, verticesAux_cons,
        List.cons.injEq, true_and]
      change (hexCSCoordPath c' (hexHeadingTurn
        (hexCSHeadingFin h0) t) ts).map hexAWPos = _
      rw [← hexCSHeadingFin_turn h0 t ht]
      simpa only [m', hcur] using hi


theorem hexCS_mem_of_two_incident_mids
    {T L : ℕ} (c : HexAWCoord) (e f : Fin 3)
    (hef : e ≠ f)
    (he : hexAWMid c e ∈ hexCSMids T L)
    (hf : hexAWMid c f ∈ hexCSMids T L) :
    c ∈ hexCSVertexSet T L := by
  rw [hexCSMids, Finset.mem_biUnion] at he
  obtain ⟨v, _, hv⟩ := he
  rw [Finset.mem_image] at hv
  obtain ⟨g, _, hg⟩ := hv
  rcases (hexAWMid_eq_iff c v.1 e g).mp hg.symm with
      ⟨hvc, _⟩ | ⟨hvn, hge⟩
  · exact hvc ▸ v.2
  · by_contra hc
    let E : HexCSIncidence T L := ⟨v, e⟩
    have hboundary : E ∈ hexCSBoundaryIncidences T L := by
      rw [hexCS_mem_boundary_iff]
      unfold hexCSIsInterior E
      simpa [E, hvn, hexAWNeighbor_invol] using hc
    have houter : hexAWNeighbor E.vtx.1 E.edge = c := by
      simp only [E]
      rw [hvn, hexAWNeighbor_invol]
    have hfm : hexAWMid (hexAWNeighbor E.vtx.1 E.edge) f ∈
        hexCSMids T L := by simpa [houter] using hf
    have hfe : f = E.edge :=
      (hexCSOutsideBoundary_mid_mem_iff E hboundary f).mp hfm
    exact hef (by simpa [E] using hfe.symm)


theorem hexCS_prefixCoord_mem
    {T L : ℕ} {hT : 0 < T} (ts : List ℤ)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion)
    (k : ℕ) (hk : k < ts.length) :
    hexEndpointPrefixCoord ts hadm.1.1 k ∈ hexCSVertexSet T L := by
  let c := hexEndpointPrefixCoord ts hadm.1.1 k
  have hlegalTake : ∀ u ∈ ts.take k, u = 1 ∨ u = -1 := by
    intro u hu
    exact hadm.1.1 u (List.mem_of_mem_take hu)
  have hvertex : hexInfra_midAccum hexAWStart 1 (ts.take k) +
      halfStep (hexInfra_headAccum 1 (ts.take k)) = hexAWPos c := by
    simpa [hexJordan_vertexPos, c] using
      hexEndpointPrefixCoord_pos ts hadm.1.1 k
  obtain ⟨e, he⟩ := hexEndpoint_mid_incident_aw
    (ts.take k) c hlegalTake hvertex
  let t := ts[k]
  have ht : t = 1 ∨ t = -1 :=
    hadm.1.1 t (List.getElem_mem hk)
  obtain ⟨f, hfe, hf⟩ := hexEndpoint_next_mid_of_forward_vertex
    (ts.take k) t c e hlegalTake ht he hvertex
  have htake : ts.take k ++ [t] = ts.take (k + 1) :=
    (List.take_succ_eq_append_getElem hk).symm
  rw [htake] at hf
  have hpassE : PassesThrough hexAWStart 1 ts (hexAWMid c e) := by
    rw [← he]
    exact hexEndpoint_prefix_mid_mem hexAWStart 1 ts k (by omega)
  have hpassF : PassesThrough hexAWStart 1 ts (hexAWMid c f) := by
    rw [← hf]
    exact hexEndpoint_prefix_mid_mem hexAWStart 1 ts (k + 1) (by omega)
  exact hexCS_mem_of_two_incident_mids c e f hfe.symm
    (hadm.2 _ hpassE) (hadm.2 _ hpassF)


theorem hexCS_endpointVertex_inside
    {T L : ℕ} {hT : 0 < T} (ts : List ℤ)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion)
    (x : ℂ) (hx : x ∈ (ofTurns hexAWStart 1 ts).endpointVertices) :
    ∃ c : HexAWCoord, c ∈ hexCSVertexSet T L ∧ x = hexAWPos c := by
  change x ∈ (verticesAux hexAWStart 1 ts).dropLast at hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨k, hk, hx⟩ := hx
  have hklt : k < ts.length := by
    rw [List.length_dropLast, length_verticesAux] at hk
    omega
  have hfullLen : k < (verticesAux hexAWStart 1 ts).length := by
    rw [length_verticesAux]
    omega
  have hget := hexJordan_verticesAux_getElem?_eq
    hexAWStart 1 ts k (by omega)
  rw [List.getElem?_eq_getElem hfullLen, Option.some.injEq] at hget
  have hxpos : x = hexJordan_vertexPos hexAWStart 1 ts k := by
    unfold hexJordan_vertexPos
    rw [← hget, ← hx]
    exact List.getElem_dropLast hk
  let c := hexEndpointPrefixCoord ts hadm.1.1 k
  refine ⟨c, hexCS_prefixCoord_mem ts hadm k hklt, ?_⟩
  rw [hxpos, hexEndpointPrefixCoord_pos ts hadm.1.1 k]


theorem hexCS_outer_ne_outsideStart
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (hne : e ≠ hexCSStartIncidence T L hT) :
    hexAWNeighbor e.vtx.1 e.edge ≠ hexCSOutsideStartCoord := by
  intro hout
  have hmidMem : hexAWMid hexCSOutsideStartCoord e.edge ∈
      hexCSMids T L := by
    rw [← hout, hexAWMid_neighbor]
    rw [hexCSMids, Finset.mem_biUnion]
    refine ⟨e.vtx, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e.edge, Finset.mem_univ _, rfl⟩
  have hedge : e.edge = 0 :=
    (hexCSOutsideStart_mid_mem_iff T L hT e.edge).mp hmidMem
  have hcoord : e.vtx.1 = hexAWOriginCoord := by
    have h := congrArg (fun c => hexAWNeighbor c e.edge) hout
    change hexAWNeighbor (hexAWNeighbor e.vtx.1 e.edge) e.edge =
      hexAWNeighbor hexCSOutsideStartCoord e.edge at h
    rw [hexAWNeighbor_invol, hedge] at h
    simpa [hexCSOutsideStartCoord, hexAWNeighbor] using h
  apply hne
  rw [HexIncidence.mk.injEq]
  exact ⟨Subtype.ext hcoord, hedge⟩


theorem hexCS_full_isSAW
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (ofTurns hexAWStart 1 ts).IsSAW := by
  apply hexEndpoint_isSAW_of_lookahead_fresh
    hexAWStart 1 ts hadm.1.2
  intro hlook
  obtain ⟨c, hc, hpos⟩ :=
    hexCS_endpointVertex_inside ts ⟨hadm.1, hadm.2.1⟩ _ hlook
  have hexit := hexCS_endpoint_boundary_exit e ts he hne hadm
  have houter : hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor e.vtx.1 e.edge) := by
    calc
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e) := hexit
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexAWHeading e.vtx.1 e.edge) := by
        rw [hexCSCanonicalHeading_halfStep]
      _ = hexAWPos (hexAWNeighbor e.vtx.1 e.edge) :=
        (hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge).symm
  have hcoord : c = hexAWNeighbor e.vtx.1 e.edge := by
    apply hexAWPos_injective
    rw [← hpos, houter]
  exact (hexCSOutsideBoundary_not_mem e he) (hcoord ▸ hc)


theorem hexCS_outsideStart_not_mem_vertices
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    hexAWPos hexCSOutsideStartCoord ∉
      (ofTurns hexAWStart 1 ts).vertices := by
  rw [hexEndpoint_vertices_eq_append_lookahead]
  simp only [List.mem_append, List.mem_singleton, not_or]
  constructor
  · intro hs
    obtain ⟨c, hc, hpos⟩ :=
      hexCS_endpointVertex_inside ts ⟨hadm.1, hadm.2.1⟩ _ hs
    have hcoord : c = hexCSOutsideStartCoord :=
      hexAWPos_injective (hpos.symm)
    rw [hcoord, hexCS_mem_vertexSet_iff] at hc
    simp [hexCSOutsideStartCoord, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong] at hc
  · intro hs
    have hexit := hexCS_endpoint_boundary_exit e ts he hne hadm
    have hposOuter : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
        hexAWPos (hexAWNeighbor e.vtx.1 e.edge) := by
      calc
        _ = hexAWMid e.vtx.1 e.edge +
            halfStep (hexCSCanonicalHeading e) := hexit
        _ = hexAWMid e.vtx.1 e.edge +
            halfStep (hexAWHeading e.vtx.1 e.edge) := by
          rw [hexCSCanonicalHeading_halfStep]
        _ = hexAWPos (hexAWNeighbor e.vtx.1 e.edge) :=
          (hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge).symm
    have hcoord : hexAWNeighbor e.vtx.1 e.edge =
        hexCSOutsideStartCoord := by
      apply hexAWPos_injective
      rw [← hposOuter]
      exact hs.symm
    exact hexCS_outer_ne_outsideStart e hne hcoord

@[simp] theorem hexCSCoordPath_start_pos (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexCSCoordPath hexCSOutsideStartCoord
        (hexCSHeadingFin 1) ts).map hexAWPos =
      hexAWPos hexCSOutsideStartCoord ::
        verticesAux hexAWStart 1 ts := by
  apply hexCSCoordPath_pos hexCSOutsideStartCoord hexAWStart 1 ts
    hexCSHeadingFits_start
  · rw [hexCSHeadingFin_one]
    change hexAWStart = hexAWMid hexCSOutsideStartCoord 0
    exact hexCSOutsideStart_mid_zero.symm
  · exact hlegal


theorem hexCSCoordPath_start_nodup
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) ts).Nodup := by
  have hfull := hexCS_full_isSAW e ts he hne hadm
  change (verticesAux hexAWStart 1 ts).Nodup at hfull
  have hout := hexCS_outsideStart_not_mem_vertices e ts he hne hadm
  change hexAWPos hexCSOutsideStartCoord ∉
    verticesAux hexAWStart 1 ts at hout
  have hmapped : ((hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) ts).map hexAWPos).Nodup := by
    rw [hexCSCoordPath_start_pos ts hadm.1.1]
    exact List.nodup_cons.mpr ⟨hout, hfull⟩
  exact (List.nodup_map_iff hexAWPos_injective).mp hmapped


theorem hexCSBrickDirections_vertices_nodup
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (ons_pathVertices (hexCSBrickDirections 1 ts)).Nodup := by
  have hc := hexCSCoordPath_start_nodup e ts he hne hadm
  have hinj : Function.Injective (fun q : HexAWCoord =>
      hexBrickPos q - hexBrickPos hexCSOutsideStartCoord) := by
    intro c d hcd
    apply hexBrickPos_injective
    rw [Prod.ext_iff] at hcd ⊢
    constructor <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at hcd ⊢ <;> omega
  have hmapped := hc.map hinj
  rw [hexCSCoordPath_brick hexCSOutsideStartCoord 1 ts
    hexCSHeadingFits_start hadm.1.1] at hmapped
  exact hmapped


theorem hexCSCoordPath_mem_cases
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (ts : List ℤ) (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (q : HexAWCoord)
    (hq : q ∈ hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) ts) :
    q = hexCSOutsideStartCoord ∨ q ∈ hexCSVertexSet T L ∨
      q = hexAWNeighbor e.vtx.1 e.edge := by
  have hpos : hexAWPos q ∈
      (hexCSCoordPath hexCSOutsideStartCoord
        (hexCSHeadingFin 1) ts).map hexAWPos :=
    List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [hexCSCoordPath_start_pos ts hadm.1.1] at hpos
  simp only [List.mem_cons] at hpos
  rcases hpos with hstart | hverts
  · left
    exact hexAWPos_injective hstart
  change hexAWPos q ∈ (ofTurns hexAWStart 1 ts).vertices at hverts
  rw [hexEndpoint_vertices_eq_append_lookahead] at hverts
  simp only [List.mem_append, List.mem_singleton] at hverts
  rcases hverts with hphysical | hlook
  · obtain ⟨c, hc, hpc⟩ :=
      hexCS_endpointVertex_inside ts ⟨hadm.1, hadm.2.1⟩ _ hphysical
    right; left
    have hqc : q = c := hexAWPos_injective hpc
    exact hqc ▸ hc
  · right; right
    have hexit := hexCS_endpoint_boundary_exit e ts he hne hadm
    apply hexAWPos_injective
    calc
      hexAWPos q = hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) := hlook
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e) := hexit
      _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexAWHeading e.vtx.1 e.edge) := by
        rw [hexCSCanonicalHeading_halfStep]
      _ = hexAWPos (hexAWNeighbor e.vtx.1 e.edge) :=
        (hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge).symm


end
end StatMech.Universality
