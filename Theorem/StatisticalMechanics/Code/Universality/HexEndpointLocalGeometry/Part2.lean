/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Structure.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

theorem hexEndpoint_local_crossing_of_internal_mid
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3) (k : ℕ)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hk : k < ts.length)
    (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid c e) :
    Nonempty (HexEndpointLocalCrossing ts c) := by
  have htakeLegal : ∀ u ∈ ts.take k, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_take hu)
  rcases hexEndpoint_forward_vertex_of_mid (ts.take k) c e
      htakeLegal hmid with hforward | hforward
  · let t := ts[k]
    have ht : t = 1 ∨ t = -1 := hlegal.1 t (List.getElem_mem hk)
    obtain ⟨f, hfe, hnext⟩ :=
      hexEndpoint_next_mid_of_forward_vertex
        (ts.take k) t c e htakeLegal ht hmid hforward
    refine ⟨⟨k, hk, e, f, hfe.symm, hmid, hforward, ?_⟩⟩
    rw [List.take_succ_eq_append_getElem hk]
    simpa only [t] using hnext
  · have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := by omega
      subst k
      simp only [List.take_zero, hexInfra_midAccum_nil] at hmid
      have hedge : hexAWMid hexAWOriginCoord 0 = hexAWMid c e :=
        hexAWMid_origin_zero.trans hmid
      rcases (hexAWMid_eq_iff hexAWOriginCoord c 0 e).mp hedge with
          ⟨hc, he⟩ | ⟨hc, he⟩
      · subst c
        subst e
        have hstartForward : hexAWStart + halfStep 1 =
            hexAWPos hexAWOriginCoord := by
          simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
            show hexUnit 4 = -hexUnit 1 by
              simpa using hexUnit_add_three 1]
        have hpos : hexAWPos hexAWOriginCoord =
            hexAWPos (hexAWNeighbor hexAWOriginCoord 0) :=
          hstartForward.symm.trans hforward
        exact hexAWNeighbor_ne hexAWOriginCoord 0
          (hexAWPos_injective hpos).symm
      · exact hnotOutside hc
    let p := k - 1
    have hp : p < ts.length := by dsimp [p]; omega
    have hpk : p + 1 = k := by dsimp [p]; omega
    let t := ts[p]
    have ht : t = 1 ∨ t = -1 := hlegal.1 t (List.getElem_mem hp)
    have hpLegal : ∀ u ∈ ts.take p, u = 1 ∨ u = -1 := by
      intro u hu
      exact hlegal.1 u (List.mem_of_mem_take hu)
    have htakeK : ts.take k = ts.take p ++ [t] := by
      rw [← List.take_succ_eq_append_getElem hp, hpk]
    obtain ⟨f, hfe, hprev⟩ :=
      hexEndpoint_previous_mid_of_forward_outer
        (ts.take p) t c e hpLegal ht
          (by simpa only [htakeK] using hmid)
          (by simpa only [htakeK] using hforward)
    have hvertex : hexInfra_midAccum hexAWStart 1 (ts.take p) +
        halfStep (hexInfra_headAccum 1 (ts.take p)) = hexAWPos c := by
      have hstep := hexCyclic_midAccum_append_single
        hexAWStart 1 t (ts.take p)
      have hback : hexInfra_midAccum hexAWStart 1 (ts.take k) -
          halfStep (hexInfra_headAccum 1 (ts.take k)) = hexAWPos c := by
        have hedge := hexEndpoint_edge_endpoint_cases
          (ts.take k) c e htakeLegal hmid
        rcases hedge with hedge | hedge
        · have hpos : hexAWPos (hexAWNeighbor c e) = hexAWPos c :=
            hforward.symm.trans hedge.1
          exact (hexAWNeighbor_ne c e (hexAWPos_injective hpos)).elim
        · exact hedge.2
      have hhead : hexInfra_headAccum 1 (ts.take p ++ [t]) =
          hexInfra_headAccum 1 (ts.take p) + t := by
        simp [hexInfra_headAccum_eq_add_sum, List.sum_append]
        ring
      rw [htakeK] at hback
      rw [hhead] at hback
      linear_combination -hstep + hback
    refine ⟨⟨p, hp, f, e, hfe, hprev, hvertex, ?_⟩⟩
    rw [hpk]
    exact hmid


theorem hexEndpoint_local_crossing_of_count_three
    (ts : List ℤ) (c : HexAWCoord) (endEdge : Fin 3)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    Nonempty (HexEndpointLocalCrossing ts c) := by
  let other := hexCyclicSucc endEdge
  have hother : other ≠ endEdge := by
    dsimp [other]
    fin_cases endEdge <;> decide
  have hpass := hexAW_all_mids_of_specialMidCount_three ts c hcount other
  obtain ⟨k, hk, hmid⟩ :=
    (hexEndpoint_passes_iff_prefix ts (hexAWMid c other)).mp hpass
  have hklt : k < ts.length := by
    by_contra hnlt
    have hkeq : k = ts.length := by omega
    have hfinal : hexInfra_midAccum hexAWStart 1 (ts.take k) =
        hexAWMid c endEdge := by
      rw [hkeq, List.take_length]
      rw [← hexInfra_endMid_eq_midAccum]
      exact hend
    exact hother (hexAWMid_edge_injective c (hmid.symm.trans hfinal))
  exact hexEndpoint_local_crossing_of_internal_mid
    ts c other k hnotOutside hlegal hklt hmid


theorem HexEndpointLocalCrossing.internal_index_cases
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (e : Fin 3) (k : ℕ) (hk : k < ts.length)
    (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid c e) :
    k = C.index ∨ k = C.index + 1 := by
  have htakeLegal : ∀ u ∈ ts.take k, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_take hu)
  rcases hexEndpoint_edge_endpoint_cases
      (ts.take k) c e htakeLegal hmid with hedge | hedge
  · left
    by_contra hne
    apply hexEndpoint_vertexPos_ne_of_saw ts hlegal.2
      k C.index hk C.index_lt hne
    unfold hexJordan_vertexPos
    exact hedge.1.trans C.at_vertex.symm
  · have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := by omega
      subst k
      simp only [List.take_zero, hexInfra_midAccum_nil] at hmid
      have hsame : hexAWMid hexAWOriginCoord 0 = hexAWMid c e :=
        hexAWMid_origin_zero.trans hmid
      rcases (hexAWMid_eq_iff hexAWOriginCoord c 0 e).mp hsame with
          ⟨hc, he⟩ | ⟨hc, he⟩
      · subst c
        subst e
        have hstartForward : hexAWStart + halfStep 1 =
            hexAWPos hexAWOriginCoord := by
          simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
            show hexUnit 4 = -hexUnit 1 by
              simpa using hexUnit_add_three 1]
        have hpos : hexAWPos hexAWOriginCoord =
            hexAWPos (hexAWNeighbor hexAWOriginCoord 0) :=
          hstartForward.symm.trans hedge.1
        exact hexAWNeighbor_ne hexAWOriginCoord 0
          (hexAWPos_injective hpos).symm
      · exact hnotOutside hc
    right
    have hkm1 : k - 1 < ts.length := by omega
    have hvertex : hexJordan_vertexPos hexAWStart 1 ts (k - 1) =
        hexAWPos c := by
      have hv := hexEndpoint_vertexPos_eq_nextMid_sub ts (k - 1) (by omega)
      have hsucc : k - 1 + 1 = k := by omega
      rw [hsucc] at hv
      exact hv.trans hedge.2
    have heq : k - 1 = C.index := by
      by_contra hne
      exact (hexEndpoint_vertexPos_ne_of_saw ts hlegal.2
        (k - 1) C.index hkm1 C.index_lt hne)
          (hvertex.trans C.at_vertex.symm)
    omega


theorem HexEndpointLocalCrossing.exists_third
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c) :
    ∃ e : Fin 3, e ≠ C.before ∧ e ≠ C.after := by
  rcases C with ⟨index, index_lt, before, after, hne,
    before_mid, at_vertex, after_mid⟩
  change ∃ e : Fin 3, e ≠ before ∧ e ≠ after
  fin_cases before <;> fin_cases after <;>
    simp_all <;>
    first | exact ⟨0, by decide, by decide⟩ |
      exact ⟨1, by decide, by decide⟩ |
      exact ⟨2, by decide, by decide⟩


theorem HexEndpointLocalCrossing.endEdge_ne
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    endEdge ≠ C.before ∧ endEdge ≠ C.after := by
  obtain ⟨third, hthirdBefore, hthirdAfter⟩ := C.exists_third
  have hpass := hexAW_all_mids_of_specialMidCount_three ts c hcount third
  obtain ⟨k, hk, hmid⟩ :=
    (hexEndpoint_passes_iff_prefix ts (hexAWMid c third)).mp hpass
  have hkeq : k = ts.length := by
    by_contra hne
    have hklt : k < ts.length := by omega
    rcases C.internal_index_cases hnotOutside hlegal third k hklt hmid with
        hkp | hks
    · subst k
      exact hthirdBefore (hexAWMid_edge_injective c
        (hmid.symm.trans C.before_mid))
    · subst k
      exact hthirdAfter (hexAWMid_edge_injective c
        (hmid.symm.trans C.after_mid))
  have hfinal : hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid c endEdge := by
    rw [hkeq, List.take_length]
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  have hthirdEnd : third = endEdge :=
    hexAWMid_edge_injective c (hmid.symm.trans hfinal)
  exact ⟨fun h => hthirdBefore (hthirdEnd.trans h),
    fun h => hthirdAfter (hthirdEnd.trans h)⟩


theorem HexEndpointLocalCrossing.endpoint_lookahead
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
  have hendMid : hexInfra_midAccum hexAWStart 1 ts =
      hexAWMid c endEdge := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  rcases hexEndpoint_forward_vertex_of_mid ts c endEdge hlegal.1
      hendMid with hforward | hforward
  · exact hforward
  · have hnpos : 0 < ts.length :=
      lt_of_le_of_lt (Nat.zero_le C.index) C.index_lt
    have hlastLt : ts.length - 1 < ts.length := by omega
    have hedge := hexEndpoint_edge_endpoint_cases
      ts c endEdge hlegal.1 hendMid
    have hback : hexInfra_midAccum hexAWStart 1 ts -
        halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
      rcases hedge with hedge | hedge
      · have hpos : hexAWPos (hexAWNeighbor c endEdge) = hexAWPos c :=
          hforward.symm.trans hedge.1
        exact (hexAWNeighbor_ne c endEdge (hexAWPos_injective hpos)).elim
      · exact hedge.2
    have hlastVertex :
        hexJordan_vertexPos hexAWStart 1 ts (ts.length - 1) =
          hexAWPos c := by
      have hv := hexEndpoint_vertexPos_eq_nextMid_sub
        ts (ts.length - 1) (by omega)
      have hsucc : ts.length - 1 + 1 = ts.length := by omega
      rw [hsucc, List.take_length] at hv
      exact hv.trans hback
    have hindex : ts.length - 1 = C.index := by
      by_contra hne
      exact (hexEndpoint_vertexPos_ne_of_saw ts hlegal.2
        (ts.length - 1) C.index hlastLt C.index_lt hne)
          (hlastVertex.trans C.at_vertex.symm)
    have hlen : ts.length = C.index + 1 := by omega
    have hfinalAfter : hexAWMid c endEdge = hexAWMid c C.after := by
      rw [← hendMid, ← C.after_mid, ← hlen, List.take_length]
    have := (C.endEdge_ne hnotOutside hlegal endEdge hend hcount).2
    exact (this (hexAWMid_edge_injective c hfinalAfter)).elim


theorem hexEndpoint_kTwo_last_vertex_aw
    (base : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
    (hneStart : hexAWMid c e ≠ hexAWStart)
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2) :
    hexInfra_midAccum hexAWStart 1 base +
      halfStep (hexInfra_headAccum 1 base) = hexAWPos c := by
  have happ := (endpointIsLegalSAW_append_one_iff
    hexAWStart 1 base t).mp hlegal
  have hfresh := hexEndpoint_final_mid_fresh_aw
    base t c e hlegal hend hneStart
  obtain ⟨f, hfe, hfBase⟩ := hexEndpoint_count_two_other_base_mid
    base t c e hend hfresh hcount
  have hendMid : hexInfra_midAccum hexAWStart 1 (base ++ [t]) =
      hexAWMid c e := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  have hmids : (ofTurns hexAWStart 1 (base ++ [t])).mids =
      (ofTurns hexAWStart 1 base).mids ++ [hexAWMid c e] := by
    change midsAux hexAWStart 1 (base ++ [t]) =
      midsAux hexAWStart 1 base ++ [hexAWMid c e]
    rw [hexCyclic_midsAux_append_single]
    rw [hexCyclic_midAccum_append_single] at hendMid
    rw [hendMid]
  have passBaseFull {z : ℂ}
      (hz : PassesThrough hexAWStart 1 base z) :
      PassesThrough hexAWStart 1 (base ++ [t]) z := by
    unfold PassesThrough at hz ⊢
    rw [hmids, List.mem_append]
    exact Or.inl hz
  have heFull : PassesThrough hexAWStart 1 (base ++ [t])
      (hexAWMid c e) :=
    hexClass_endsAt_passesThrough (base ++ [t]) (hexAWMid c e) hend
  have threeImpossible (g : Fin 3) (hgf : g ≠ f) (hge : g ≠ e)
      (hgBase : PassesThrough hexAWStart 1 base (hexAWMid c g)) : False := by
    have hfFull := passBaseFull hfBase
    have hgFull := passBaseFull hgBase
    have hall : ∀ l : Fin 3,
        PassesThrough hexAWStart 1 (base ++ [t]) (hexAWMid c l) := by
      intro l
      fin_cases e <;> fin_cases f <;> fin_cases g <;> fin_cases l <;>
        simp_all
    have hthree := hexAW_specialMidCount_three_of_all
      (base ++ [t]) c hall
    omega
  unfold PassesThrough HexWalk.mids at hfBase
  change hexAWMid c f ∈ midsAux hexAWStart 1 base at hfBase
  rw [List.mem_iff_getElem] at hfBase
  obtain ⟨k, hklist, hkget⟩ := hfBase
  have hk : k ≤ base.length := by
    rw [length_midsAux] at hklist
    omega
  have hget := hexJordan_midsAux_getElem?_eq hexAWStart 1 base k hk
  rw [List.getElem?_eq_getElem hklist, Option.some.injEq] at hget
  have hmid : hexInfra_midAccum hexAWStart 1 (base.take k) =
      hexAWMid c f := hget.symm.trans hkget
  by_cases hkzero : k = 0
  · subst k
    simp only [List.take_zero, hexInfra_midAccum_nil] at hmid
    have hedge : hexAWMid hexAWOriginCoord 0 = hexAWMid c f := by
      rw [hexAWMid_origin_zero]
      exact hmid
    rcases (hexAWMid_eq_iff hexAWOriginCoord c 0 f).mp hedge with
        ⟨hc, hf0⟩ | ⟨hc, hf0⟩
    · subst c
      subst f
      rcases base with _ | ⟨u, us⟩
      · simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
          show hexUnit 4 = -hexUnit 1 by simpa using hexUnit_add_three 1]
      · have hu : u = 1 ∨ u = -1 := happ.1.1 u (by simp)
        have hstartForward : hexAWStart + halfStep 1 =
            hexAWPos hexAWOriginCoord := by
          simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
            show hexUnit 4 = -hexUnit 1 by simpa using hexUnit_add_three 1]
        obtain ⟨g, hgf, hg⟩ := hexEndpoint_next_mid_of_forward_vertex
          [] u hexAWOriginCoord 0 (by simp) hu
          (by simpa using hexAWMid_origin_zero.symm) hstartForward
        have hgBase : PassesThrough hexAWStart 1 (u :: us)
            (hexAWMid hexAWOriginCoord g) := by
          have hp := hexEndpoint_prefix_mid_mem hexAWStart 1 (u :: us) 1 (by simp)
          rw [← hg]
          simpa using hp
        have hge : g ≠ e := by
          intro hge
          apply hfresh
          simpa [hge] using hgBase
        exact (threeImpossible g hgf hge hgBase).elim
    · exact (hnotOutside hc).elim
  · by_cases hklast : k = base.length
    · have hbaseMid : hexInfra_midAccum hexAWStart 1 base =
          hexAWMid c f := by
        simpa [hklast] using hmid
      rcases hexEndpoint_edge_endpoint_cases base c f happ.1.1 hbaseMid with
          hforward | hforward
      · exact hforward.1
      · rcases List.eq_nil_or_concat base with hnil | ⟨s, u, hbase⟩
        · subst base
          exact (hkzero (by simpa using hklast)).elim
        · subst base
          have hu : u = 1 ∨ u = -1 := happ.1.1 u (by simp)
          have hslegal : ∀ q ∈ s, q = 1 ∨ q = -1 := by
            intro q hq
            exact happ.1.1 q (by simp [hq])
          obtain ⟨g, hgf, hg⟩ :=
            hexEndpoint_previous_mid_of_forward_outer
              s u c f hslegal hu
                (by simpa only [List.concat_eq_append] using hbaseMid)
                (by simpa only [List.concat_eq_append] using hforward.1)
          have hgBase : PassesThrough hexAWStart 1 (s ++ [u])
              (hexAWMid c g) := by
            have hp := hexEndpoint_prefix_mid_mem
              hexAWStart 1 (s ++ [u]) s.length (by simp)
            rw [← hg]
            simpa using hp
          have hge : g ≠ e := by
            intro hge
            apply hfresh
            simpa [hge] using hgBase
          exact (threeImpossible g hgf hge
            (by simpa only [List.concat_eq_append] using hgBase)).elim
    · have hklt : k < base.length := by omega
      obtain ⟨g, hgf, hgBase⟩ :=
        hexEndpoint_internal_mid_forces_second
          base c f k (by omega) hklt happ.1.1 hmid
      have hge : g ≠ e := by
        intro hge
        apply hfresh
        simpa [hge] using hgBase
      exact (threeImpossible g hgf hge hgBase).elim


theorem hexEndpoint_count_one_forward_vertex_aw
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c e))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 1) :
    hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
  have hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  rcases hexEndpoint_forward_vertex_of_mid ts c e hlegal.1 hmid with
      hforward | hforward
  · exact hforward
  · rcases List.eq_nil_or_concat ts with rfl | ⟨s, t, rfl⟩
    · have hedge : hexAWMid hexAWOriginCoord 0 = hexAWMid c e :=
        hexAWMid_origin_zero.trans hmid
      rcases (hexAWMid_eq_iff hexAWOriginCoord c 0 e).mp hedge with
          ⟨hc, he⟩ | ⟨hc, he⟩
      · subst c
        subst e
        have hstartForward : hexAWStart + halfStep 1 =
            hexAWPos hexAWOriginCoord := by
          simp [hexAWStart, halfStep, hexAWOriginCoord, hexAWPos,
            show hexUnit 4 = -hexUnit 1 by
              simpa using hexUnit_add_three 1]
        have hpos : hexAWPos hexAWOriginCoord =
            hexAWPos (hexAWNeighbor hexAWOriginCoord 0) :=
          hstartForward.symm.trans hforward
        exact (hexAWNeighbor_ne hexAWOriginCoord 0
          (hexAWPos_injective hpos).symm).elim
      · exact (hnotOutside hc).elim
    · have ht : t = 1 ∨ t = -1 := hlegal.1 t (by simp)
      have hslegal : ∀ u ∈ s, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal.1 u (by simp [hu])
      obtain ⟨f, hfe, hprev⟩ :=
        hexEndpoint_previous_mid_of_forward_outer
          s t c e hslegal ht
            (by simpa only [List.concat_eq_append] using hmid)
            (by simpa only [List.concat_eq_append] using hforward)
      have hepass : PassesThrough hexAWStart 1 (s ++ [t])
          (hexAWMid c e) :=
        hexClass_endsAt_passesThrough (s ++ [t]) (hexAWMid c e)
          (by simpa only [List.concat_eq_append] using hend)
      have hfpass : PassesThrough hexAWStart 1 (s ++ [t])
          (hexAWMid c f) := by
        rw [← hprev]
        have hp := hexEndpoint_prefix_mid_mem
          hexAWStart 1 (s ++ [t]) s.length (by simp)
        simpa using hp
      have htwo := specialMidCount_ge_two_of_labels
        hexAWStart 1 (hexAWPos c)
        (hexAWMid c 0 - hexAWPos c) (s ++ [t]) e f hfe.symm
        (by simpa only [hexAW_labelMid_eq_mid] using hepass)
        (by simpa only [hexAW_labelMid_eq_mid] using hfpass)
      have hcount' : specialMidCount hexAWStart 1 (hexAWPos c)
          (hexAWMid c 0 - hexAWPos c) (s ++ [t]) = 1 := by
        simpa only [List.concat_eq_append] using hcount
      omega


end
end StatMech.Universality
