/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

theorem hexEndpoint_vertexPos_ne_of_saw
    (ts : List ℤ) (hsaw : (ofTurns hexAWStart 1 ts).EndpointIsSAW)
    (i j : ℕ) (hi : i < ts.length) (hj : j < ts.length) (hne : i ≠ j) :
    hexJordan_vertexPos hexAWStart 1 ts i ≠
      hexJordan_vertexPos hexAWStart 1 ts j := by
  intro heq
  have hilen : i < (verticesAux hexAWStart 1 ts).length := by
    rw [length_verticesAux]
    omega
  have hjlen : j < (verticesAux hexAWStart 1 ts).length := by
    rw [length_verticesAux]
    omega
  have hidrop : i < (verticesAux hexAWStart 1 ts).dropLast.length := by
    rw [List.length_dropLast, length_verticesAux]
    omega
  have hjdrop : j < (verticesAux hexAWStart 1 ts).dropLast.length := by
    rw [List.length_dropLast, length_verticesAux]
    omega
  have hvi := hexJordan_verticesAux_getElem?_eq
    hexAWStart 1 ts i (le_of_lt hi)
  have hvj := hexJordan_verticesAux_getElem?_eq
    hexAWStart 1 ts j (le_of_lt hj)
  rw [List.getElem?_eq_getElem hilen, Option.some.injEq] at hvi
  rw [List.getElem?_eq_getElem hjlen, Option.some.injEq] at hvj
  have hget : (verticesAux hexAWStart 1 ts).dropLast[i] =
      (verticesAux hexAWStart 1 ts).dropLast[j] := by
    rw [List.getElem_dropLast hidrop, List.getElem_dropLast hjdrop,
      hvi, hvj]
    exact heq
  exact hne ((List.getElem_inj hsaw).mp hget)


theorem hexEndpoint_vertexPos_eq_nextMid_sub
    (ts : List ℤ) (k : ℕ) (hk : k < ts.length) :
    hexJordan_vertexPos hexAWStart 1 ts k =
      hexInfra_midAccum hexAWStart 1 (ts.take (k + 1)) -
        halfStep (hexInfra_headAccum 1 (ts.take (k + 1))) := by
  rw [List.take_succ_eq_append_getElem hk,
    hexCyclic_midAccum_append_single]
  unfold hexJordan_vertexPos
  simp only [hexInfra_headAccum_eq_add_sum, List.sum_append,
    List.sum_singleton]
  ring


theorem hexEndpoint_edge_endpoint_cases
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e) :
    (hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) = hexAWPos c ∧
        hexInfra_midAccum hexAWStart 1 ts -
          halfStep (hexInfra_headAccum 1 ts) =
            hexAWPos (hexAWNeighbor c e)) ∨
      (hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) =
            hexAWPos (hexAWNeighbor c e) ∧
        hexInfra_midAccum hexAWStart 1 ts -
          halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) := by
  rcases hexEndpoint_forward_vertex_of_mid ts c e hlegal hmid with
      hforward | hforward
  · left
    refine ⟨hforward, ?_⟩
    unfold hexAWMid at hmid
    linear_combination 2 * hmid - hforward
  · right
    refine ⟨hforward, ?_⟩
    unfold hexAWMid at hmid
    linear_combination 2 * hmid - hforward


theorem hexEndpoint_final_mid_fresh_aw
    (base : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
    (hne : hexAWMid c e ≠ hexAWStart) :
    ¬PassesThrough hexAWStart 1 base (hexAWMid c e) := by
  intro hpass
  unfold PassesThrough HexWalk.mids at hpass
  change hexAWMid c e ∈ midsAux hexAWStart 1 base at hpass
  rw [List.mem_iff_getElem] at hpass
  obtain ⟨k, hklist, hkget⟩ := hpass
  have hk : k ≤ base.length := by
    rw [length_midsAux] at hklist
    omega
  have hget := hexJordan_midsAux_getElem?_eq hexAWStart 1 base k hk
  rw [List.getElem?_eq_getElem hklist, Option.some.injEq] at hget
  have hmid : hexInfra_midAccum hexAWStart 1 (base.take k) =
      hexAWMid c e := hget.symm.trans hkget
  have hkpos : 0 < k := by
    by_contra hkzero
    have : k = 0 := by omega
    subst k
    simp only [List.take_zero, hexInfra_midAccum_nil] at hmid
    exact hne hmid.symm
  have ht : t = 1 ∨ t = -1 :=
    hlegal.1 t (by simp)
  have hfullMid : hexInfra_midAccum hexAWStart 1 (base ++ [t]) =
      hexAWMid c e := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  by_cases hklast : k = base.length
  · have hbaseMid : hexInfra_midAccum hexAWStart 1 base =
        hexAWMid c e := by
      simpa [hklast] using hmid
    have hnew := hexCyclic_midAccum_append_single hexAWStart 1 t base
    have hsame : hexInfra_midAccum hexAWStart 1 (base ++ [t]) =
        hexInfra_midAccum hexAWStart 1 base := hfullMid.trans hbaseMid.symm
    apply hexW1_halfStep_add_ne_zero (hexInfra_headAccum 1 base) t ht
    linear_combination -hnew + hsame
  · have hklt : k < base.length := by omega
    let full := base ++ [t]
    have hfullLegal : ∀ u ∈ full, u = 1 ∨ u = -1 := hlegal.1
    have htakeLegal : ∀ u ∈ full.take k, u = 1 ∨ u = -1 := by
      intro u hu
      exact hfullLegal u (List.mem_of_mem_take hu)
    have htakeMid : hexInfra_midAccum hexAWStart 1 (full.take k) =
        hexAWMid c e := by
      simpa [full, List.take_append_of_le_length hk] using hmid
    have hearly := hexEndpoint_edge_endpoint_cases
      (full.take k) c e htakeLegal htakeMid
    have hfinal := hexEndpoint_edge_endpoint_cases
      full c e hfullLegal (by simpa [full] using hfullMid)
    have hfinalPos : hexJordan_vertexPos hexAWStart 1 full base.length =
        hexInfra_midAccum hexAWStart 1 full -
          halfStep (hexInfra_headAccum 1 full) := by
      have h := hexEndpoint_vertexPos_eq_nextMid_sub
        full base.length (by simp [full])
      have htake : full.take (base.length + 1) = full := by
        rw [show base.length + 1 = full.length by simp [full], List.take_length]
      rw [htake] at h
      exact h
    have hcurPos : hexJordan_vertexPos hexAWStart 1 full k =
        hexInfra_midAccum hexAWStart 1 (full.take k) +
          halfStep (hexInfra_headAccum 1 (full.take k)) := rfl
    have hpredPos : hexJordan_vertexPos hexAWStart 1 full (k - 1) =
        hexInfra_midAccum hexAWStart 1 (full.take k) -
          halfStep (hexInfra_headAccum 1 (full.take k)) := by
      have h := hexEndpoint_vertexPos_eq_nextMid_sub full (k - 1) (by
        simp [full]
        omega)
      have hkback : k - 1 + 1 = k := by omega
      rw [hkback] at h
      exact h
    have hfinalLt : base.length < full.length := by simp [full]
    have hcurLt : k < full.length := by simp [full]; omega
    have hpredLt : k - 1 < full.length := by simp [full]; omega
    rcases hearly with hearly | hearly <;>
      rcases hfinal with hfinal | hfinal
    · apply (hexEndpoint_vertexPos_ne_of_saw full hlegal.2
        base.length (k - 1) hfinalLt hpredLt (by omega))
      rw [hfinalPos, hpredPos, hfinal.2, hearly.2]
    · apply (hexEndpoint_vertexPos_ne_of_saw full hlegal.2
        base.length k hfinalLt hcurLt (by omega))
      rw [hfinalPos, hcurPos, hfinal.2, hearly.1]
    · apply (hexEndpoint_vertexPos_ne_of_saw full hlegal.2
        base.length k hfinalLt hcurLt (by omega))
      rw [hfinalPos, hcurPos, hfinal.2, hearly.1]
    · apply (hexEndpoint_vertexPos_ne_of_saw full hlegal.2
        base.length (k - 1) hfinalLt hpredLt (by omega))
      rw [hfinalPos, hpredPos, hfinal.2, hearly.2]


theorem hexAWMid_edge_injective (c : HexAWCoord) :
    Function.Injective (hexAWMid c) := by
  intro e f hef
  rcases (hexAWMid_eq_iff c c e f).mp hef with h | h
  · exact h.2.symm
  · exact h.2.symm


theorem hexEndpoint_count_two_other_base_mid
    (base : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hend : (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
    (hnew : ¬PassesThrough hexAWStart 1 base (hexAWMid c e))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2) :
    ∃ f : Fin 3, f ≠ e ∧
      PassesThrough hexAWStart 1 base (hexAWMid c f) := by
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
  have hpassFull (f : Fin 3) :
      PassesThrough hexAWStart 1 (base ++ [t]) (hexAWMid c f) ↔
        PassesThrough hexAWStart 1 base (hexAWMid c f) ∨ f = e := by
    unfold PassesThrough
    rw [hmids, List.mem_append, List.mem_singleton]
    exact or_congr_right (hexAWMid_edge_injective c |>.eq_iff)
  have hlabel0 : hexAWPos c + (hexAWMid c 0 - hexAWPos c) =
      hexAWMid c 0 := by ring
  have hlabel1 : hexAWPos c +
      hexOmega * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 1 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 1
  have hlabel2 : hexAWPos c +
      hexOmega ^ 2 * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 2 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 2
  simp only [specialMidCount] at hcount
  rw [hlabel0, hlabel1, hlabel2, hpassFull 0, hpassFull 1,
    hpassFull 2] at hcount
  fin_cases e
  · by_cases h1 : PassesThrough hexAWStart 1 base (hexAWMid c 1)
    · exact ⟨1, by decide, h1⟩
    · have h2 : PassesThrough hexAWStart 1 base (hexAWMid c 2) := by
        by_contra hn2
        simp_all
      exact ⟨2, by decide, h2⟩
  · by_cases h0 : PassesThrough hexAWStart 1 base (hexAWMid c 0)
    · exact ⟨0, by decide, h0⟩
    · have h2 : PassesThrough hexAWStart 1 base (hexAWMid c 2) := by
        by_contra hn2
        simp_all
      exact ⟨2, by decide, h2⟩
  · by_cases h0 : PassesThrough hexAWStart 1 base (hexAWMid c 0)
    · exact ⟨0, by decide, h0⟩
    · have h1 : PassesThrough hexAWStart 1 base (hexAWMid c 1) := by
        by_contra hn1
        simp_all
      exact ⟨1, by decide, h1⟩


theorem hexAW_specialMidCount_three_of_all
    (ts : List ℤ) (c : HexAWCoord)
    (hall : ∀ e : Fin 3,
      PassesThrough hexAWStart 1 ts (hexAWMid c e)) :
    specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3 := by
  have hlabel0 : hexAWPos c + (hexAWMid c 0 - hexAWPos c) =
      hexAWMid c 0 := by ring
  have hlabel1 : hexAWPos c +
      hexOmega * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 1 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 1
  have hlabel2 : hexAWPos c +
      hexOmega ^ 2 * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 2 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 2
  unfold specialMidCount
  rw [hlabel0, hlabel1, hlabel2]
  simp [hall]


theorem hexAW_all_mids_of_specialMidCount_three
    (ts : List ℤ) (c : HexAWCoord)
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    ∀ e : Fin 3, PassesThrough hexAWStart 1 ts (hexAWMid c e) := by
  have hlabel0 : hexAWPos c + (hexAWMid c 0 - hexAWPos c) =
      hexAWMid c 0 := by ring
  have hlabel1 : hexAWPos c +
      hexOmega * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 1 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 1
  have hlabel2 : hexAWPos c +
      hexOmega ^ 2 * (hexAWMid c 0 - hexAWPos c) = hexAWMid c 2 := by
    simpa [labelMid] using hexAW_labelMid_eq_mid c 2
  simp only [specialMidCount, hlabel0, hlabel1, hlabel2] at hcount
  intro e
  fin_cases e <;>
    by_cases h0 : PassesThrough hexAWStart 1 ts (hexAWMid c 0) <;>
    by_cases h1 : PassesThrough hexAWStart 1 ts (hexAWMid c 1) <;>
    by_cases h2 : PassesThrough hexAWStart 1 ts (hexAWMid c 2) <;>
    simp_all


theorem hexEndpoint_passes_iff_prefix
    (ts : List ℤ) (z : ℂ) :
    PassesThrough hexAWStart 1 ts z ↔
      ∃ k, k ≤ ts.length ∧
        hexInfra_midAccum hexAWStart 1 (ts.take k) = z := by
  constructor
  · intro hz
    unfold PassesThrough HexWalk.mids at hz
    change z ∈ midsAux hexAWStart 1 ts at hz
    rw [List.mem_iff_getElem] at hz
    obtain ⟨k, hklen, hk⟩ := hz
    have hkle : k ≤ ts.length := by
      rw [length_midsAux] at hklen
      omega
    have hget := hexJordan_midsAux_getElem?_eq
      hexAWStart 1 ts k hkle
    rw [List.getElem?_eq_getElem hklen, Option.some.injEq] at hget
    exact ⟨k, hkle, hget.symm.trans hk⟩
  · rintro ⟨k, hk, rfl⟩
    exact hexEndpoint_prefix_mid_mem hexAWStart 1 ts k hk


end
end StatMech.Universality
