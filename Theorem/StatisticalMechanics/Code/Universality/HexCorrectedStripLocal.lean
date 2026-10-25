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


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCS_anchored_partner_valid
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (base tail : List ℤ)
    (hvalid : (ofTurns a h0 (base ++ ((1 : ℤ) :: tail))).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ ((1 : ℤ) :: tail))).StaysIn region)
    (hsum : ((1 : ℤ) :: tail).sum = -4)
    (hclose :
      let m := hexInfra_midAccum a h0 base
      let h := hexInfra_headAccum h0 base
      hexInfra_midAccum m h ((1 : ℤ) :: tail) +
        halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
          m + halfStep h) :
    (ofTurns a h0
        (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).EndpointIsLegalSAW ∧
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).StaysIn region ∧
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).EndsAt
          (hexInfra_midAccum a h0 base +
            halfStep (hexInfra_headAccum h0 base) +
            halfStep (hexInfra_headAccum h0 base + 1)) := by
  let m := hexInfra_midAccum a h0 base
  let h := hexInfra_headAccum h0 base
  let q := (verticesAux m h ((1 : ℤ) :: tail)).dropLast
  let r := (verticesAux m h
    (anchoredLoopReverse ((1 : ℤ) :: tail))).dropLast
  have hblockLegal : ∀ t ∈ (1 : ℤ) :: tail,
      t = 1 ∨ t = -1 := by
    intro t ht
    exact hvalid.1.1 t (by simp [ht])
  have hbaseLegal : ∀ t ∈ base, t = 1 ∨ t = -1 := by
    intro t ht
    exact hvalid.1.1 t (by simp [ht])
  have hpartnerLegal :
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).LegalTurns := by
    intro t ht
    simp only [ofTurns_turns, List.mem_append] at ht
    rcases ht with ht | ht
    · exact hbaseLegal t ht
    · exact anchoredLoopReverse_legal _ hblockLegal t ht
  have hqform : q = (m + halfStep h) ::
      (verticesAux (m + halfStep h + halfStep (h + 1))
        (h + 1) tail).dropLast := by
    change (verticesAux m h ((1 : ℤ) :: tail)).dropLast = _
    rw [verticesAux_cons, List.dropLast_cons_of_ne_nil
      (hexInfra_verticesAux_ne_nil _ _ _)]
  have hrform : r = (m + halfStep h) :: q.tail.reverse := by
    change (verticesAux m h
      (anchoredLoopReverse ((1 : ℤ) :: tail))).dropLast = _
    rw [anchoredLoopReverse_endpointVertices_eq
      m h tail hblockLegal hsum hclose]
  have hsourceSaw :
      ((verticesAux a h0 base).dropLast ++ q).Nodup := by
    have hs := hvalid.1.2
    change (verticesAux a h0
      (base ++ ((1 : ℤ) :: tail))).dropLast.Nodup at hs
    rw [hexEndpoint_dropLast_verticesAux_append] at hs
    simpa only [m, h, q] using hs
  have hpartnerSaw :
      ((verticesAux a h0 base).dropLast ++ r).Nodup := by
    rw [List.nodup_append] at hsourceSaw ⊢
    rcases hsourceSaw with ⟨hb, hqnodup, hdisj⟩
    refine ⟨hb, ?_, ?_⟩
    · change r.Nodup
      rw [hqform] at hqnodup
      rw [hrform, hqform]
      rw [List.nodup_cons] at hqnodup ⊢
      exact ⟨by simpa using hqnodup.1,
        List.nodup_reverse.mpr hqnodup.2⟩
    · intro x hx y hy
      apply hdisj x hx y
      change y ∈ r at hy
      rw [hrform, hqform] at hy
      rw [hqform]
      simpa using hy
  have hpartnerEndpointSaw :
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).EndpointIsSAW := by
    change (verticesAux a h0
      (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).dropLast.Nodup
    rw [hexEndpoint_dropLast_verticesAux_append]
    simpa only [m, h, r] using hpartnerSaw
  have hpartnerStay :
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).StaysIn region := by
    intro z hz
    change z ∈ midsAux a h0
      (base ++ anchoredLoopReverse ((1 : ℤ) :: tail)) at hz
    rw [hexEndpoint_midsAux_append] at hz
    apply hvalid.2 z
    change z ∈ midsAux a h0 (base ++ ((1 : ℤ) :: tail))
    rw [hexEndpoint_midsAux_append]
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ hz
    · apply List.mem_append_right _
      have hmids := anchoredLoopReverse_midsAux_eq
        m h tail hblockLegal hsum hclose
      rw [hmids] at hz
      rw [midsAux_cons]
      simpa using hz
  have hpartnerEnds :
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).EndsAt
          (m + halfStep h + halfStep (h + 1)) := by
    unfold HexWalk.EndsAt
    rw [hexInfra_endMid_eq_midAccum, hexJordan_midAccum_append]
    exact anchoredLoopReverse_midAccum_eq
      m h tail hblockLegal hsum hclose
  exact ⟨⟨hpartnerLegal, hpartnerEndpointSaw⟩,
    hpartnerStay, by simpa [m, h] using hpartnerEnds⟩


theorem hexCS_midAccum_add_six (m : ℂ) (h : ℤ) (ts : List ℤ) :
    hexInfra_midAccum m (h + 6) ts = hexInfra_midAccum m h ts := by
  induction ts generalizing m h with
  | nil => rfl
  | cons t ts ih =>
      rw [hexInfra_midAccum_cons, hexInfra_midAccum_cons]
      rw [hexEndpoint_halfStep_add_six,
        show h + 6 + t = (h + t) + 6 by ring,
        hexEndpoint_halfStep_add_six]
      exact ih _ _


theorem hexCS_midsAux_add_six (m : ℂ) (h : ℤ) (ts : List ℤ) :
    midsAux m (h + 6) ts = midsAux m h ts := by
  induction ts generalizing m h with
  | nil => rfl
  | cons t ts ih =>
      rw [midsAux_cons, midsAux_cons]
      rw [hexEndpoint_halfStep_add_six,
        show h + 6 + t = (h + t) + 6 by ring,
        hexEndpoint_halfStep_add_six]
      exact congrArg (List.cons m) (ih _ _)


theorem hexCS_verticesAux_add_six (m : ℂ) (h : ℤ) (ts : List ℤ) :
    verticesAux m (h + 6) ts = verticesAux m h ts := by
  induction ts generalizing m h with
  | nil =>
      simp only [verticesAux_nil]
      rw [hexEndpoint_halfStep_add_six]
  | cons t ts ih =>
      rw [verticesAux_cons, verticesAux_cons]
      rw [hexEndpoint_halfStep_add_six,
        show h + 6 + t = (h + t) + 6 by ring,
        hexEndpoint_halfStep_add_six]
      exact congrArg (List.cons (m + halfStep h)) (ih _ _)


theorem hexCS_anchoredLoopReverse_midsAux_eq_neg
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (-1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((-1 : ℤ) :: tail).sum = 4)
    (hclose : hexInfra_midAccum m h ((-1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) =
        m + halfStep h) :
    midsAux m h (anchoredLoopReverse ((-1 : ℤ) :: tail)) =
      m :: (midsAux m h ((-1 : ℤ) :: tail)).tail.reverse := by
  let m1 := m + halfStep h + halfStep (h - 1)
  let H := hexInfra_headAccum (h - 1) tail
  let M := hexInfra_midAccum m1 (h - 1) tail
  have htail : ∀ t ∈ tail, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (by simp [ht])
  have hH : H = h + 4 := by
    dsimp [H]
    simp only [hexInfra_headAccum_eq_add_sum, List.sum_cons] at hsum ⊢
    omega
  have hclose' : M + halfStep H = m + halfStep h := by
    simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons, M, H, m1,
      show h + (-1 : ℤ) = h - 1 by ring] using hclose
  have hopp : halfStep (h + 1) = -halfStep H := by
    rw [hH, show h + 4 = (h + 1) + 3 by ring,
      hexEndpoint_halfStep_add_three]
    ring
  have hfirst : m + halfStep h + halfStep (h + 1) = M := by
    rw [hopp]
    linear_combination -hclose'
  have hheading : H + 3 = h + 1 + 6 := by rw [hH]; ring
  rw [anchoredLoopReverse_cons, midsAux_cons]
  rw [show -(-1 : ℤ) = 1 by norm_num, hfirst]
  rw [← hexCS_midsAux_add_six M (h + 1) (loopReverse tail),
    ← hheading]
  rw [hexEndpoint_midsAux_loopReverse_exact m1 (h - 1) tail htail]
  simp only [midsAux_cons, List.tail_cons]
  rfl


theorem hexCS_anchoredLoopReverse_midAccum_eq_neg
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (-1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((-1 : ℤ) :: tail).sum = 4)
    (hclose : hexInfra_midAccum m h ((-1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) =
        m + halfStep h) :
    hexInfra_midAccum m h
        (anchoredLoopReverse ((-1 : ℤ) :: tail)) =
      m + halfStep h + halfStep (h - 1) := by
  have htrace := hexCS_anchoredLoopReverse_midsAux_eq_neg
    m h tail hlegal hsum hclose
  have hlast := congrArg List.getLast? htrace
  rw [hexInfra_midsAux_getLast?] at hlast
  simp only [midsAux_cons, List.tail_cons] at hlast
  rw [List.getLast?_cons] at hlast
  have hhead :
      (midsAux (m + halfStep h + halfStep (h - 1))
        (h - 1) tail).head?.getD m =
          m + halfStep h + halfStep (h - 1) := by
    cases tail <;> rfl
  rw [show h + (-1 : ℤ) = h - 1 by ring] at hlast
  rw [List.getLast?_reverse, hhead] at hlast
  exact Option.some.inj hlast


theorem hexCS_anchoredLoopReverse_verticesAux_eq_neg
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (-1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((-1 : ℤ) :: tail).sum = 4)
    (hclose : hexInfra_midAccum m h ((-1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) =
        m + halfStep h) :
    verticesAux m h (anchoredLoopReverse ((-1 : ℤ) :: tail)) =
      (m + halfStep h) ::
        (verticesAux m h ((-1 : ℤ) :: tail)).dropLast.tail.reverse ++
          [m + halfStep h] := by
  let m1 := m + halfStep h + halfStep (h - 1)
  let H := hexInfra_headAccum (h - 1) tail
  let M := hexInfra_midAccum m1 (h - 1) tail
  have htail : ∀ t ∈ tail, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (by simp [ht])
  have hH : H = h + 4 := by
    dsimp [H]
    simp only [hexInfra_headAccum_eq_add_sum, List.sum_cons] at hsum ⊢
    omega
  have hclose' : M + halfStep H = m + halfStep h := by
    simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons, M, H, m1,
      show h + (-1 : ℤ) = h - 1 by ring] using hclose
  have hopp : halfStep (h + 1) = -halfStep H := by
    rw [hH, show h + 4 = (h + 1) + 3 by ring,
      hexEndpoint_halfStep_add_three]
    ring
  have hfirst : m + halfStep h + halfStep (h + 1) = M := by
    rw [hopp]
    linear_combination -hclose'
  have hheading : H + 3 = h + 1 + 6 := by rw [hH]; ring
  rw [anchoredLoopReverse_cons, verticesAux_cons]
  rw [show -(-1 : ℤ) = 1 by norm_num, hfirst]
  rw [← hexCS_verticesAux_add_six M (h + 1) (loopReverse tail),
    ← hheading]
  rw [hexEndpoint_verticesAux_loopReverse_exact m1 (h - 1) tail htail]
  have hback : m1 - halfStep (h - 1) = m + halfStep h := by
    dsimp [m1]
    ring
  rw [hback]
  have hn : verticesAux m1 (h - 1) tail ≠ [] :=
    hexInfra_verticesAux_ne_nil m1 (h - 1) tail
  change (m + halfStep h) ::
      ((verticesAux m1 (h - 1) tail).dropLast.reverse ++
        [m + halfStep h]) =
    (m + halfStep h) ::
      (((m + halfStep h) :: verticesAux m1 (h - 1) tail).dropLast.tail.reverse ++
        [m + halfStep h])
  rw [List.dropLast_cons_of_ne_nil hn, List.tail_cons]

theorem hexCS_anchoredLoopReverse_endpointVertices_eq_neg
    (m : ℂ) (h : ℤ) (tail : List ℤ)
    (hlegal : ∀ t ∈ (-1 : ℤ) :: tail, t = 1 ∨ t = -1)
    (hsum : ((-1 : ℤ) :: tail).sum = 4)
    (hclose : hexInfra_midAccum m h ((-1 : ℤ) :: tail) +
      halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) =
        m + halfStep h) :
    (verticesAux m h
        (anchoredLoopReverse ((-1 : ℤ) :: tail))).dropLast =
      (m + halfStep h) ::
        (verticesAux m h ((-1 : ℤ) :: tail)).dropLast.tail.reverse := by
  rw [hexCS_anchoredLoopReverse_verticesAux_eq_neg
    m h tail hlegal hsum hclose]
  rw [List.dropLast_append_of_ne_nil
    (by simp : [m + halfStep h] ≠ []), List.dropLast_singleton,
    List.append_nil]


theorem hexCS_anchored_partner_valid_neg
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (base tail : List ℤ)
    (hvalid : (ofTurns a h0 (base ++ ((-1 : ℤ) :: tail))).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ ((-1 : ℤ) :: tail))).StaysIn region)
    (hsum : ((-1 : ℤ) :: tail).sum = 4)
    (hclose :
      let m := hexInfra_midAccum a h0 base
      let h := hexInfra_headAccum h0 base
      hexInfra_midAccum m h ((-1 : ℤ) :: tail) +
        halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) =
          m + halfStep h) :
    (ofTurns a h0
        (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).EndpointIsLegalSAW ∧
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).StaysIn region ∧
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).EndsAt
          (hexInfra_midAccum a h0 base +
            halfStep (hexInfra_headAccum h0 base) +
            halfStep (hexInfra_headAccum h0 base - 1)) := by
  let m := hexInfra_midAccum a h0 base
  let h := hexInfra_headAccum h0 base
  let q := (verticesAux m h ((-1 : ℤ) :: tail)).dropLast
  let r := (verticesAux m h
    (anchoredLoopReverse ((-1 : ℤ) :: tail))).dropLast
  have hblockLegal : ∀ t ∈ (-1 : ℤ) :: tail,
      t = 1 ∨ t = -1 := by
    intro t ht
    exact hvalid.1.1 t (by simp [ht])
  have hbaseLegal : ∀ t ∈ base, t = 1 ∨ t = -1 := by
    intro t ht
    exact hvalid.1.1 t (by simp [ht])
  have hpartnerLegal :
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).LegalTurns := by
    intro t ht
    simp only [ofTurns_turns, List.mem_append] at ht
    rcases ht with ht | ht
    · exact hbaseLegal t ht
    · exact anchoredLoopReverse_legal _ hblockLegal t ht
  have hqform : q = (m + halfStep h) ::
      (verticesAux (m + halfStep h + halfStep (h - 1))
        (h - 1) tail).dropLast := by
    change (verticesAux m h ((-1 : ℤ) :: tail)).dropLast = _
    rw [verticesAux_cons, List.dropLast_cons_of_ne_nil
      (hexInfra_verticesAux_ne_nil _ _ _)]
    rw [show h + (-1 : ℤ) = h - 1 by ring]
  have hrform : r = (m + halfStep h) :: q.tail.reverse := by
    change (verticesAux m h
      (anchoredLoopReverse ((-1 : ℤ) :: tail))).dropLast = _
    rw [hexCS_anchoredLoopReverse_endpointVertices_eq_neg
      m h tail hblockLegal hsum hclose]
  have hsourceSaw :
      ((verticesAux a h0 base).dropLast ++ q).Nodup := by
    have hs := hvalid.1.2
    change (verticesAux a h0
      (base ++ ((-1 : ℤ) :: tail))).dropLast.Nodup at hs
    rw [hexEndpoint_dropLast_verticesAux_append] at hs
    simpa only [m, h, q] using hs
  have hpartnerSaw :
      ((verticesAux a h0 base).dropLast ++ r).Nodup := by
    rw [List.nodup_append] at hsourceSaw ⊢
    rcases hsourceSaw with ⟨hb, hqnodup, hdisj⟩
    refine ⟨hb, ?_, ?_⟩
    · change r.Nodup
      rw [hqform] at hqnodup
      rw [hrform, hqform]
      rw [List.nodup_cons] at hqnodup ⊢
      exact ⟨by simpa using hqnodup.1,
        List.nodup_reverse.mpr hqnodup.2⟩
    · intro x hx y hy
      apply hdisj x hx y
      change y ∈ r at hy
      rw [hrform, hqform] at hy
      rw [hqform]
      simpa using hy
  have hpartnerEndpointSaw :
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).EndpointIsSAW := by
    change (verticesAux a h0
      (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).dropLast.Nodup
    rw [hexEndpoint_dropLast_verticesAux_append]
    simpa only [m, h, r] using hpartnerSaw
  have hpartnerStay :
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).StaysIn region := by
    intro z hz
    change z ∈ midsAux a h0
      (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail)) at hz
    rw [hexEndpoint_midsAux_append] at hz
    apply hvalid.2 z
    change z ∈ midsAux a h0 (base ++ ((-1 : ℤ) :: tail))
    rw [hexEndpoint_midsAux_append]
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ hz
    · apply List.mem_append_right _
      have hmids := hexCS_anchoredLoopReverse_midsAux_eq_neg
        m h tail hblockLegal hsum hclose
      rw [hmids] at hz
      rw [midsAux_cons]
      simpa using hz
  have hpartnerEnds :
      (ofTurns a h0
        (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).EndsAt
          (m + halfStep h + halfStep (h - 1)) := by
    unfold HexWalk.EndsAt
    rw [hexInfra_endMid_eq_midAccum, hexJordan_midAccum_append]
    exact hexCS_anchoredLoopReverse_midAccum_eq_neg
      m h tail hblockLegal hsum hclose
  exact ⟨⟨hpartnerLegal, hpartnerEndpointSaw⟩,
    hpartnerStay, by simpa [m, h] using hpartnerEnds⟩


theorem hexCS_next_mid_turn_one
    (v du m : ℂ) (j : Fin 3) (h : ℤ)
    (hm : m = labelMid v du j)
    (hv : m + halfStep h = v) :
    m + halfStep h + halfStep (h + 1) =
      labelMid v du (hexCyclicPred j) := by
  rw [hexCyclicPred_mid, ← hm, hexEndpoint_halfStep_add_one]
  linear_combination (1 - hexOmega ^ 2) * hv

theorem hexCS_next_mid_turn_neg_one
    (v du m : ℂ) (j : Fin 3) (h : ℤ)
    (hm : m = labelMid v du j)
    (hv : m + halfStep h = v) :
    m + halfStep h + halfStep (h - 1) =
      labelMid v du (hexCyclicSucc j) := by
  rw [hexCyclicSucc_mid, ← hm, hexEndpoint_halfStep_sub_one]
  linear_combination (1 - hexOmega) * hv

theorem hexCS_fin3_eq_succ_of_ne_self_ne_pred
    (j e : Fin 3) (hself : e ≠ j) (hpred : e ≠ hexCyclicPred j) :
    e = hexCyclicSucc j := by
  fin_cases j <;> fin_cases e <;> simp_all [hexCyclicSucc, hexCyclicPred]

theorem hexCS_fin3_eq_pred_of_ne_self_ne_succ
    (j e : Fin 3) (hself : e ≠ j) (hsucc : e ≠ hexCyclicSucc j) :
    e = hexCyclicPred j := by
  fin_cases j <;> fin_cases e <;> simp_all [hexCyclicSucc, hexCyclicPred]


theorem HexEndpointLocalCrossing.after_eq_cyclic
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    (ts[C.index]'C.index_lt = 1 → C.after = hexCyclicPred C.before) ∧
      (ts[C.index]'C.index_lt = -1 → C.after = hexCyclicSucc C.before) := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let m := hexInfra_midAccum hexAWStart 1 base
  let h := hexInfra_headAccum 1 base
  have htmem : t ∈ ts := List.getElem_mem C.index_lt
  have ht : t = 1 ∨ t = -1 := hlegal.1 t htmem
  have htake : ts.take (C.index + 1) = base ++ [t] := by
    simpa only [base, t] using List.take_succ_eq_append_getElem C.index_lt
  have hnext : hexInfra_midAccum hexAWStart 1 (ts.take (C.index + 1)) =
      m + halfStep h + halfStep (h + t) := by
    rw [htake, hexCyclic_midAccum_append_single]
  have hm : m = labelMid (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) C.before := by
    rw [hexAW_labelMid_eq_mid]
    exact C.before_mid
  have hv : m + halfStep h = hexAWPos c := by
    exact C.at_vertex
  constructor
  · intro htone
    have htone' : t = 1 := by simpa only [t] using htone
    have hformula := hexCS_next_mid_turn_one
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) m C.before h hm hv
    have hmid : hexAWMid c C.after =
        hexAWMid c (hexCyclicPred C.before) := by
      calc
        hexAWMid c C.after =
            hexInfra_midAccum hexAWStart 1 (ts.take (C.index + 1)) :=
          C.after_mid.symm
        _ = m + halfStep h + halfStep (h + t) := hnext
        _ = labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
            (hexCyclicPred C.before) := by simpa only [htone'] using hformula
        _ = hexAWMid c (hexCyclicPred C.before) :=
          hexAW_labelMid_eq_mid c _
    exact hexAWMid_edge_injective c hmid
  · intro htneg
    have htneg' : t = -1 := by simpa only [t] using htneg
    have hformula := hexCS_next_mid_turn_neg_one
      (hexAWPos c) (hexAWMid c 0 - hexAWPos c) m C.before h hm hv
    have hmid : hexAWMid c C.after =
        hexAWMid c (hexCyclicSucc C.before) := by
      calc
        hexAWMid c C.after =
            hexInfra_midAccum hexAWStart 1 (ts.take (C.index + 1)) :=
          C.after_mid.symm
        _ = m + halfStep h + halfStep (h + t) := hnext
        _ = labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
            (hexCyclicSucc C.before) := by
          simpa only [htneg', sub_eq_add_neg] using hformula
        _ = hexAWMid c (hexCyclicSucc C.before) :=
          hexAW_labelMid_eq_mid c _
    exact hexAWMid_edge_injective c hmid


theorem HexEndpointLocalCrossing.endEdge_eq_cyclic
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    (ts[C.index]'C.index_lt = 1 → endEdge = hexCyclicSucc C.before) ∧
      (ts[C.index]'C.index_lt = -1 → endEdge = hexCyclicPred C.before) := by
  have hendNe := C.endEdge_ne hnotOutside hlegal endEdge hend hcount
  have hafter := C.after_eq_cyclic hlegal
  constructor
  · intro ht
    apply hexCS_fin3_eq_succ_of_ne_self_ne_pred C.before endEdge hendNe.1
    exact fun he => hendNe.2 (he.trans (hafter.1 ht).symm)
  · intro ht
    apply hexCS_fin3_eq_pred_of_ne_self_ne_succ C.before endEdge hendNe.1
    exact fun he => hendNe.2 (he.trans (hafter.2 ht).symm)


theorem hexCS_cyclicLoopPair_of_selected_terminal_cycle
    {T L : ℕ} {hT : 0 < T}
    (c : HexAWCoord) (endEdge : Fin 3) (ts : List ℤ)
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3)
    (horient :
      (ts[C.index]'C.index_lt = 1 ∧ (ts.drop C.index).sum = -4) ∨
      (ts[C.index]'C.index_lt = -1 ∧ (ts.drop C.index).sum = 4)) :
    ∃ P : HexEndpointCyclicLoopPair
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c),
      ts ∈ P.piece ∧
        hexInfra_midAccum hexAWStart 1 P.base +
          halfStep (hexInfra_headAccum 1 P.base) = hexAWPos c ∧
        ∀ u ∈ P.piece,
          specialMidCount hexAWStart 1 (hexAWPos c)
            (hexAWMid c 0 - hexAWPos c) u = 3 := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let m := hexInfra_midAccum hexAWStart 1 base
  let h := hexInfra_headAccum 1 base
  have hdrop : ts.drop C.index = t :: tail := by
    simpa only [t, tail] using List.drop_eq_getElem_cons C.index_lt
  have hsplit : ts = base ++ t :: tail := by
    calc
      ts = ts.take C.index ++ ts.drop C.index :=
        (List.take_append_drop C.index ts).symm
      _ = base ++ t :: tail := by rw [hdrop]
  have hm : m = labelMid (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) C.before := by
    rw [hexAW_labelMid_eq_mid]
    exact C.before_mid
  have hv : m + halfStep h = hexAWPos c := C.at_vertex
  have hclose : hexInfra_midAccum m h (t :: tail) +
      halfStep (hexInfra_headAccum h (t :: tail)) = m + halfStep h := by
    have hlook := C.endpoint_lookahead
      hnotOutside hadm.1 endEdge hadm.2.2 hcount
    rw [hsplit, hexJordan_midAccum_append,
      hexJordan_headAccum_append] at hlook
    exact hlook.trans hv.symm
  have hlabels := C.endEdge_eq_cyclic
    hnotOutside hadm.1 endEdge hadm.2.2 hcount
  rcases horient with hpos | hneg
  · have ht : t = 1 := by simpa only [t] using hpos.1
    have hsum : ((1 : ℤ) :: tail).sum = -4 := by
      rw [hdrop] at hpos
      simpa only [ht] using hpos.2
    have hsplit' : ts = base ++ (1 : ℤ) :: tail := by
      simpa only [ht] using hsplit
    have hclose' : hexInfra_midAccum m h ((1 : ℤ) :: tail) +
        halfStep (hexInfra_headAccum h ((1 : ℤ) :: tail)) =
          m + halfStep h := by simpa only [ht] using hclose
    have hsource :
        (ofTurns hexAWStart 1 (base ++ ((1 : ℤ) :: tail))).EndpointIsLegalSAW ∧
          (ofTurns hexAWStart 1 (base ++ ((1 : ℤ) :: tail))).StaysIn
            (hexCSFiniteRegion T L hT).inRegion := by
      simpa only [← hsplit'] using ⟨hadm.1, hadm.2.1⟩
    have hpartner := hexCS_anchored_partner_valid
      (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
      base tail hsource hsum hclose'
    have hqEnd :
        (ofTurns hexAWStart 1 (base ++ ((1 : ℤ) :: tail))).EndsAt
          (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
            (hexCyclicSucc C.before)) := by
      rw [hexAW_labelMid_eq_mid]
      have hendEq := hlabels.1 hpos.1
      simpa only [← hsplit', hendEq] using hadm.2.2
    have hpMid : m + halfStep h + halfStep (h + 1) =
        labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
          (hexCyclicPred C.before) :=
      hexCS_next_mid_turn_one _ _ _ _ _ hm hv
    have hrEnd :
        (ofTurns hexAWStart 1
          (base ++ anchoredLoopReverse ((1 : ℤ) :: tail))).EndsAt
          (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
            (hexCyclicPred C.before)) := by
      rw [← hpMid]
      simpa only [m, h] using hpartner.2.2
    have hblockLegal : ∀ u ∈ (1 : ℤ) :: tail,
        u = 1 ∨ u = -1 := by
      intro u hu
      exact hsource.1.1 u (by simp [hu])
    have hpasses : ∀ z : ℂ,
        PassesThrough hexAWStart 1
            (base ++ anchoredLoopReverse ((1 : ℤ) :: tail)) z ↔
          PassesThrough hexAWStart 1 (base ++ (1 : ℤ) :: tail) z := by
      intro z
      unfold PassesThrough HexWalk.mids
      change z ∈ midsAux hexAWStart 1
          (base ++ anchoredLoopReverse ((1 : ℤ) :: tail)) ↔
        z ∈ midsAux hexAWStart 1 (base ++ (1 : ℤ) :: tail)
      rw [hexEndpoint_midsAux_append, hexEndpoint_midsAux_append,
        anchoredLoopReverse_midsAux_eq m h tail hblockLegal hsum hclose']
      simp [m, h, midsAux_cons]
    have hpartnerCount : specialMidCount hexAWStart 1 (hexAWPos c)
        (hexAWMid c 0 - hexAWPos c)
          (base ++ anchoredLoopReverse ((1 : ℤ) :: tail)) = 3 := by
      unfold specialMidCount at hcount ⊢
      rw [hpasses, hpasses, hpasses]
      rw [← hsplit']
      exact hcount
    let P : HexEndpointCyclicLoopPair
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) := {
      baseLabel := C.before
      base := base
      loopQ := (1 : ℤ) :: tail
      loopQ_first := ⟨tail, rfl⟩
      loopQ_sum := hsum
      succ_valid := ⟨hsource.1, hsource.2, hqEnd⟩
      pred_valid := ⟨hpartner.1, hpartner.2.1, by
        simpa only [hexEndpointLoopPartner_eq_anchored] using hrEnd⟩ }
    refine ⟨P, ?_, ?_, ?_⟩
    · simp [P, HexEndpointCyclicLoopPair.piece, ← hsplit']
    · simpa only [P, base, m, h] using hv
    · intro u hu
      simp only [P, HexEndpointCyclicLoopPair.piece,
        Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · rw [← hsplit']
        exact hcount
      · simpa only [hexEndpointLoopPartner_eq_anchored] using hpartnerCount
  · have ht : t = -1 := by simpa only [t] using hneg.1
    have hsum : ((-1 : ℤ) :: tail).sum = 4 := by
      rw [hdrop] at hneg
      simpa only [ht] using hneg.2
    have hsplit' : ts = base ++ (-1 : ℤ) :: tail := by
      simpa only [ht] using hsplit
    have hclose' : hexInfra_midAccum m h ((-1 : ℤ) :: tail) +
        halfStep (hexInfra_headAccum h ((-1 : ℤ) :: tail)) =
          m + halfStep h := by simpa only [ht] using hclose
    have hsource :
        (ofTurns hexAWStart 1 (base ++ ((-1 : ℤ) :: tail))).EndpointIsLegalSAW ∧
          (ofTurns hexAWStart 1 (base ++ ((-1 : ℤ) :: tail))).StaysIn
            (hexCSFiniteRegion T L hT).inRegion := by
      simpa only [← hsplit'] using ⟨hadm.1, hadm.2.1⟩
    have hpartner := hexCS_anchored_partner_valid_neg
      (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
      base tail hsource hsum hclose'
    have hpMid : m + halfStep h + halfStep (h - 1) =
        labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
          (hexCyclicSucc C.before) :=
      hexCS_next_mid_turn_neg_one _ _ _ _ _ hm hv
    have hqEnd :
        (ofTurns hexAWStart 1
          (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail))).EndsAt
          (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
            (hexCyclicSucc C.before)) := by
      rw [← hpMid]
      simpa only [m, h] using hpartner.2.2
    have hrEnd :
        (ofTurns hexAWStart 1 (base ++ ((-1 : ℤ) :: tail))).EndsAt
          (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
            (hexCyclicPred C.before)) := by
      rw [hexAW_labelMid_eq_mid]
      have hendEq := hlabels.2 hneg.1
      simpa only [← hsplit', hendEq] using hadm.2.2
    have hblockLegal : ∀ u ∈ (-1 : ℤ) :: tail,
        u = 1 ∨ u = -1 := by
      intro u hu
      exact hsource.1.1 u (by simp [hu])
    have hpasses : ∀ z : ℂ,
        PassesThrough hexAWStart 1
            (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail)) z ↔
          PassesThrough hexAWStart 1 (base ++ (-1 : ℤ) :: tail) z := by
      intro z
      unfold PassesThrough HexWalk.mids
      change z ∈ midsAux hexAWStart 1
          (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail)) ↔
        z ∈ midsAux hexAWStart 1 (base ++ (-1 : ℤ) :: tail)
      rw [hexEndpoint_midsAux_append, hexEndpoint_midsAux_append,
        hexCS_anchoredLoopReverse_midsAux_eq_neg
          m h tail hblockLegal hsum hclose']
      simp [m, h, midsAux_cons]
    have hpartnerCount : specialMidCount hexAWStart 1 (hexAWPos c)
        (hexAWMid c 0 - hexAWPos c)
          (base ++ anchoredLoopReverse ((-1 : ℤ) :: tail)) = 3 := by
      unfold specialMidCount at hcount ⊢
      rw [hpasses, hpasses, hpasses]
      rw [← hsplit']
      exact hcount
    let P : HexEndpointCyclicLoopPair
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c) := {
      baseLabel := C.before
      base := base
      loopQ := anchoredLoopReverse ((-1 : ℤ) :: tail)
      loopQ_first := ⟨loopReverse tail, by
        simp [anchoredLoopReverse]⟩
      loopQ_sum := by
        rw [anchoredLoopReverse_sum, hsum]
      succ_valid := ⟨hpartner.1, hpartner.2.1, hqEnd⟩
      pred_valid := by
        rw [hexEndpointLoopPartner_eq_anchored,
          anchoredLoopReverse_involutive]
        exact ⟨hsource.1, hsource.2, hrEnd⟩ }
    refine ⟨P, ?_, ?_, ?_⟩
    · simp [P, HexEndpointCyclicLoopPair.piece,
        hexEndpointLoopPartner_eq_anchored]
      right
      rw [loopReverse_involutive]
      exact hsplit'
    · simpa only [P, base, m, h] using hv
    · intro u hu
      simp only [P, HexEndpointCyclicLoopPair.piece,
        Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hpartnerCount
      · rw [hexEndpointLoopPartner_eq_anchored,
          anchoredLoopReverse_involutive]
        rw [← hsplit']
        exact hcount


theorem hexCSHeadingFin_eq_of_halfStep_eq
    (h k : ℤ) (heq : halfStep h = halfStep k) :
    hexCSHeadingFin h = hexCSHeadingFin k := by
  have hd : (6 : ℤ) ∣ h - k :=
    (hexUnit_eq_iff_mod h k).mp (hexInfra_halfStep_inj heq)
  obtain ⟨a, ha⟩ := hexCSHeadingFin_dvd h
  obtain ⟨b, hb⟩ := hexCSHeadingFin_dvd k
  obtain ⟨q, hq⟩ := hd
  apply Fin.ext
  have hh := (hexCSHeadingFin h).isLt
  have hk := (hexCSHeadingFin k).isLt
  push_cast at ha hb hh hk
  omega

theorem hexCSHeadingFin_hexAWHeading
    (c : HexAWCoord) (e : Fin 3) :
    hexCSHeadingFin (hexAWHeading c e) = hexAWHeadingMod c e := by
  apply Fin.ext
  obtain ⟨q, hq⟩ := hexCSHeadingFin_dvd (hexAWHeading c e)
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexAWHeading, hexAWHeadingMod] at hq ⊢ <;> omega

theorem hexCSHeadingFin_three : hexCSHeadingFin 3 = 3 := by
  apply Fin.ext
  obtain ⟨q, hq⟩ := hexCSHeadingFin_dvd 3
  have hh := (hexCSHeadingFin 3).isLt
  have hz : (0 : ℤ) ≤ ((hexCSHeadingFin 3).val : ℤ) := by positivity
  norm_num at hq ⊢
  omega

theorem hexCSHeadingFin_hexAWHeading_add_three
    (c : HexAWCoord) (e : Fin 3) :
    hexCSHeadingFin (hexAWHeading c e + 3) =
      hexAWHeadingMod c e + 3 := by
  rw [hexCSHeadingFin_add, hexCSHeadingFin_hexAWHeading,
    hexCSHeadingFin_three]

theorem hexCSHeadingFits_headingMod
    (c : HexAWCoord) (e : Fin 3) :
    HexCSHeadingFits c (hexAWHeadingMod c e) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [HexCSHeadingFits, hexAWHeadingMod]

theorem hexAWHeadingMod_edge_injective (c : HexAWCoord) :
    Function.Injective (hexAWHeadingMod c) := by
  intro e f hef
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;> fin_cases f <;>
    simp [hexAWHeadingMod] at hef ⊢


theorem HexEndpointLocalCrossing.after_heading
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    let base := ts.take C.index
    let t := ts[C.index]'C.index_lt
    let h := hexInfra_headAccum 1 base
    hexCSHeadingFin (h + t) = hexAWHeadingMod c C.after := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let m := hexInfra_midAccum hexAWStart 1 base
  let h := hexInfra_headAccum 1 base
  have htake : ts.take (C.index + 1) = base ++ [t] := by
    simpa only [base, t] using List.take_succ_eq_append_getElem C.index_lt
  have hnext : hexInfra_midAccum hexAWStart 1 (ts.take (C.index + 1)) =
      m + halfStep h + halfStep (h + t) := by
    rw [htake, hexCyclic_midAccum_append_single]
  have hv : m + halfStep h = hexAWPos c := C.at_vertex
  have hmid : m + halfStep h + halfStep (h + t) =
      hexAWMid c C.after := hnext.symm.trans C.after_mid
  have hhalf : halfStep (h + t) = halfStep (hexAWHeading c C.after) := by
    have hedge := hexAWMid_sub_pos_eq_halfStep c C.after
    calc
      halfStep (h + t) =
          (m + halfStep h + halfStep (h + t)) - (m + halfStep h) := by ring
      _ = hexAWMid c C.after - hexAWPos c := by rw [hmid, hv]
      _ = halfStep (hexAWHeading c C.after) := hedge
  exact (hexCSHeadingFin_eq_of_halfStep_eq _ _ hhalf).trans
    (hexCSHeadingFin_hexAWHeading c C.after)


theorem HexEndpointLocalCrossing.edgeOf_after_heading
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    let base := ts.take C.index
    let t := ts[C.index]'C.index_lt
    let h := hexInfra_headAccum 1 base
    HexCSHeadingFits c (hexCSHeadingFin (h + t)) ∧
      hexCSEdgeOfHeading c (hexCSHeadingFin (h + t)) = C.after := by
  dsimp only
  have hh := C.after_heading hlegal
  constructor
  · rw [hh]
    exact hexCSHeadingFits_headingMod c C.after
  · apply hexAWHeadingMod_edge_injective c
    rw [hexCSEdgeOfHeading_mod]
    · exact hh
    · rw [hh]
      exact hexCSHeadingFits_headingMod c C.after


theorem HexEndpointLocalCrossing.terminalCoordPath_pos
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    let base := ts.take C.index
    let t := ts[C.index]'C.index_lt
    let tail := ts.drop (C.index + 1)
    let m := hexInfra_midAccum hexAWStart 1 base
    let h := hexInfra_headAccum 1 base
    (hexCSCoordPath c (hexCSHeadingFin (h + t)) tail).map hexAWPos =
      verticesAux m h (t :: tail) := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let m := hexInfra_midAccum hexAWStart 1 base
  let h := hexInfra_headAccum 1 base
  let m1 := m + halfStep h + halfStep (h + t)
  have hedge := C.edgeOf_after_heading hlegal
  have htail : ∀ u ∈ tail, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_drop hu)
  have htake : ts.take (C.index + 1) = base ++ [t] := by
    simpa only [base, t] using List.take_succ_eq_append_getElem C.index_lt
  have hm1 : m1 = hexAWMid c C.after := by
    calc
      m1 = hexInfra_midAccum hexAWStart 1 (ts.take (C.index + 1)) := by
        rw [htake, hexCyclic_midAccum_append_single]
      _ = hexAWMid c C.after := C.after_mid
  have hmid : m1 = hexAWMid c
      (hexCSEdgeOfHeading c (hexCSHeadingFin (h + t))) := by
    rw [hedge.2]
    exact hm1
  have hpath := hexCSCoordPath_pos c m1 (h + t) tail
    hedge.1 hmid htail
  have hm1pos : m1 = hexAWPos c + halfStep (h + t) := by
    dsimp only [m1]
    rw [C.at_vertex]
  dsimp only
  rw [hpath, verticesAux_cons]
  rw [C.at_vertex]
  rw [hm1pos]


theorem HexEndpointLocalCrossing.final_heading
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    hexCSHeadingFin (hexInfra_headAccum 1 ts) =
      hexCSHeadingFin (hexAWHeading c endEdge + 3) := by
  have hlook := C.endpoint_lookahead
    hnotOutside hlegal endEdge hend hcount
  have hendMid : hexInfra_midAccum hexAWStart 1 ts =
      hexAWMid c endEdge := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  have hout : halfStep (hexInfra_headAccum 1 ts) =
      halfStep (hexAWHeading c endEdge + 3) := by
    have hedge := hexAWMid_sub_pos_eq_halfStep c endEdge
    have hopp := hexEndpoint_halfStep_add_three (hexAWHeading c endEdge)
    rw [hendMid] at hlook
    calc
      halfStep (hexInfra_headAccum 1 ts) =
          (hexAWMid c endEdge + halfStep (hexInfra_headAccum 1 ts)) -
            hexAWMid c endEdge := by ring
      _ = hexAWPos c - hexAWMid c endEdge := by rw [hlook]
      _ = -(hexAWMid c endEdge - hexAWPos c) := by ring
      _ = -halfStep (hexAWHeading c endEdge) := by rw [hedge]
      _ = halfStep (hexAWHeading c endEdge + 3) := hopp.symm
  exact hexCSHeadingFin_eq_of_halfStep_eq _ _ hout


theorem HexEndpointLocalCrossing.closing_brick_identity
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    let base := ts.take C.index
    let t := ts[C.index]'C.index_lt
    let tail := ts.drop (C.index + 1)
    let h := hexInfra_headAccum 1 base
    let H := hexInfra_headAccum (h + t) tail
    2 * (-t) + 3 * ons_turnPow
        (hexBrickDir (hexCSHeadingFin H))
        (hexBrickDir (hexCSHeadingFin (h + t))) =
      hexBrickTurnPotential (hexCSHeadingFin (h + t)) -
        hexBrickTurnPotential (hexCSHeadingFin H) := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let h := hexInfra_headAccum 1 base
  let H := hexInfra_headAccum (h + t) tail
  have ht : t = 1 ∨ t = -1 :=
    hlegal.1 t (List.getElem_mem C.index_lt)
  have hsplit : ts = base ++ t :: tail := by
    calc
      ts = ts.take C.index ++ ts.drop C.index :=
        (List.take_append_drop C.index ts).symm
      _ = base ++ t :: tail := by
        rw [List.drop_eq_getElem_cons C.index_lt]
  have hH : H = hexInfra_headAccum 1 ts := by
    rw [hsplit, hexJordan_headAccum_append]
    rfl
  have hstart := C.after_heading hlegal
  have hstart' : hexCSHeadingFin (h + t) =
      hexAWHeadingMod c C.after := by
    simpa only [base, t, h] using hstart
  have hfinal := C.final_heading hnotOutside hlegal endEdge hend hcount
  have hlabels := C.endEdge_eq_cyclic
    hnotOutside hlegal endEdge hend hcount
  dsimp only
  change 2 * -t + 3 * ons_turnPow
      (hexBrickDir (hexCSHeadingFin H))
      (hexBrickDir (hexCSHeadingFin (h + t))) =
    hexBrickTurnPotential (hexCSHeadingFin (h + t)) -
      hexBrickTurnPotential (hexCSHeadingFin H)
  rw [hH, hfinal, hstart']
  rw [hexCSHeadingFin_hexAWHeading_add_three]
  change 2 * -t + 3 * ons_turnPow
      (hexBrickDir (hexAWHeadingMod c endEdge + 3))
      (hexBrickDir (hexAWHeadingMod c C.after)) =
    hexBrickTurnPotential (hexAWHeadingMod c C.after) -
      hexBrickTurnPotential
        (hexAWHeadingMod c endEdge + 3)
  rcases ht with ht | ht
  · have ha := (C.after_eq_cyclic hlegal).1 (by simpa only [t] using ht)
    have he := hlabels.1 (by simpa only [t] using ht)
    rw [ht, ha, he]
    rcases c with ⟨i, j, color⟩
    generalize hb : C.before = b
    cases color <;> fin_cases b <;>
      rfl
  · have ha := (C.after_eq_cyclic hlegal).2 (by simpa only [t] using ht)
    have he := hlabels.2 (by simpa only [t] using ht)
    rw [ht, ha, he]
    rcases c with ⟨i, j, color⟩
    generalize hb : C.before = b
    cases color <;> fin_cases b <;>
      rfl

theorem hexCS_map_dropLast {α β : Type*}
    (f : α → β) (xs : List α) :
    (xs.map f).dropLast = xs.dropLast.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          rw [List.map_cons,
            List.dropLast_cons_of_ne_nil
              (by simp : (List.map f (y :: ys)) ≠ []),
            List.dropLast_cons_of_ne_nil (by simp : (y :: ys) ≠ [])]
          change f x :: (List.map f (y :: ys)).dropLast =
            f x :: List.map f ((y :: ys).dropLast)
          exact congrArg (List.cons (f x)) ih


theorem HexEndpointLocalCrossing.terminalBrick_closed_nodup
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    let base := ts.take C.index
    let t := ts[C.index]'C.index_lt
    let tail := ts.drop (C.index + 1)
    let h := hexInfra_headAccum 1 base
    let dirs := hexCSBrickDirections (h + t) tail
    ons_pathDisplacement dirs = 0 ∧
      (ons_pathVertices dirs).dropLast.Nodup := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let m := hexInfra_midAccum hexAWStart 1 base
  let h := hexInfra_headAccum 1 base
  let coords := hexCSCoordPath c (hexCSHeadingFin (h + t)) tail
  let dirs := hexCSBrickDirections (h + t) tail
  have ht : t = 1 ∨ t = -1 :=
    hlegal.1 t (List.getElem_mem C.index_lt)
  have htail : ∀ u ∈ tail, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_drop hu)
  have hedge := C.edgeOf_after_heading hlegal
  have hpath : coords.map hexAWPos = verticesAux m h (t :: tail) := by
    simpa only [coords, base, t, tail, m, h] using
      C.terminalCoordPath_pos hlegal
  have hbrick : coords.map
      (fun q => hexBrickPos q - hexBrickPos c) =
        ons_pathVertices dirs := by
    simpa only [coords, dirs] using
      hexCSCoordPath_brick c (h + t) tail hedge.1 htail
  have hsplit : ts = base ++ t :: tail := by
    calc
      ts = ts.take C.index ++ ts.drop C.index :=
        (List.take_append_drop C.index ts).symm
      _ = base ++ t :: tail := by
        rw [List.drop_eq_getElem_cons C.index_lt]
  have hsuffix : (verticesAux m h (t :: tail)).dropLast.Nodup := by
    have hs := hlegal.2
    change (verticesAux hexAWStart 1 ts).dropLast.Nodup at hs
    rw [hsplit, hexEndpoint_dropLast_verticesAux_append] at hs
    exact (List.nodup_append.mp hs).2.1
  have hcoord : coords.dropLast.Nodup := by
    apply (List.nodup_map_iff hexAWPos_injective).mp
    rw [← hexCS_map_dropLast, hpath]
    exact hsuffix
  have hlook := C.endpoint_lookahead
    hnotOutside hlegal endEdge hend hcount
  have hclose : hexInfra_midAccum m h (t :: tail) +
      halfStep (hexInfra_headAccum h (t :: tail)) = hexAWPos c := by
    rw [hsplit, hexJordan_midAccum_append,
      hexJordan_headAccum_append] at hlook
    exact hlook
  have hlastMap := congrArg List.getLast? hpath
  rw [List.getLast?_map, hexInfra_verticesAux_getLast?, hclose] at hlastMap
  have hlast : coords.getLast? = some c := by
    cases hc : coords.getLast? with
    | none => simp [hc] at hlastMap
    | some q =>
        congr 1
        apply hexAWPos_injective
        simpa [hc] using hlastMap
  have hclosed : ons_pathDisplacement dirs = 0 := by
    have hb := congrArg List.getLast? hbrick
    rw [List.getLast?_map, hlast, ons_pathVertices_getLast] at hb
    have hz : hexBrickPos c - hexBrickPos c = (0 : ℤ × ℤ) := sub_self _
    simpa only [hz, Option.map_some, Option.some.injEq] using hb.symm
  have hinj : Function.Injective
      (fun q : HexAWCoord => hexBrickPos q - hexBrickPos c) := by
    intro q r hqr
    apply hexBrickPos_injective
    rw [Prod.ext_iff] at hqr ⊢
    constructor <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at hqr ⊢ <;> omega
  have hdirs : (ons_pathVertices dirs).dropLast.Nodup := by
    have hmapped := hcoord.map hinj
    rw [← hexCS_map_dropLast, hbrick] at hmapped
    exact hmapped
  exact ⟨hclosed, hdirs⟩

theorem hexCS_cyclicTurnSum_eq_open_add_close
    (dirs : List (Fin 4)) (hne : dirs ≠ []) :
    ons_cyclicTurnSum dirs = ons_openTurnSum dirs +
      ons_turnPow dirs.getLast! dirs.head! := by
  cases dirs with
  | nil => exact (hne rfl).elim
  | cons d ds => rfl


theorem HexEndpointLocalCrossing.terminalBlock_length_ge_three
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    3 ≤ (ts.drop C.index).length := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let m := hexInfra_midAccum hexAWStart 1 base
  let h := hexInfra_headAccum 1 base
  have hdrop : ts.drop C.index = t :: tail := by
    simpa only [t, tail] using List.drop_eq_getElem_cons C.index_lt
  have hsplit : ts = base ++ t :: tail := by
    calc
      ts = ts.take C.index ++ ts.drop C.index :=
        (List.take_append_drop C.index ts).symm
      _ = base ++ t :: tail := by rw [hdrop]
  have hendMid : hexInfra_midAccum hexAWStart 1 ts =
      hexAWMid c endEdge := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hend
  have hendNe := C.endEdge_ne hnotOutside hlegal endEdge hend hcount
  by_contra hthree
  have hlt : (ts.drop C.index).length < 3 := by omega
  rw [hdrop] at hlt
  rcases tail with _ | ⟨u, us⟩
  · have hidx : C.index + 1 = ts.length := by
      have hlen := congrArg List.length hsplit
      have hbaseLen : base.length = C.index := by
        simp [base, Nat.min_eq_left (Nat.le_of_lt C.index_lt)]
      simp only [List.length_append, List.length_cons, List.length_nil,
        hbaseLen] at hlen
      omega
    have htake : ts.take (C.index + 1) = ts := by
      rw [hidx, List.take_length]
    have hmid : hexAWMid c C.after = hexAWMid c endEdge := by
      calc
        hexAWMid c C.after =
            hexInfra_midAccum hexAWStart 1 (ts.take (C.index + 1)) :=
          C.after_mid.symm
        _ = hexInfra_midAccum hexAWStart 1 ts := by rw [htake]
        _ = hexAWMid c endEdge := hendMid
    exact hendNe.2 (hexAWMid_edge_injective c hmid).symm
  · rcases us with _ | ⟨v, vs⟩
    · have hsplit' : ts = base ++ [t, u] := by simpa using hsplit
      have hlook := C.endpoint_lookahead
        hnotOutside hlegal endEdge hend hcount
      have hclose : hexInfra_midAccum m h [t, u] +
          halfStep (hexInfra_headAccum h [t, u]) = m + halfStep h := by
        rw [hsplit', hexJordan_midAccum_append,
          hexJordan_headAccum_append] at hlook
        exact hlook.trans C.at_vertex.symm
      have hlocal : hexInfra_midAccum m h [t, u] =
          hexInfra_midAccum m h [t] := by
        simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil,
          hexInfra_headAccum_cons, hexInfra_headAccum_nil] at hclose ⊢
        linear_combination (1 / 2 : ℂ) * hclose
      have htake : ts.take (C.index + 1) = base ++ [t] := by
        simpa only [base, t] using List.take_succ_eq_append_getElem C.index_lt
      have hmid : hexAWMid c C.after = hexAWMid c endEdge := by
        calc
          hexAWMid c C.after =
              hexInfra_midAccum hexAWStart 1 (ts.take (C.index + 1)) :=
            C.after_mid.symm
          _ = hexInfra_midAccum hexAWStart 1 (base ++ [t]) := by rw [htake]
          _ = hexInfra_midAccum m h [t] :=
            hexJordan_midAccum_append _ _ _ _
          _ = hexInfra_midAccum m h [t, u] := hlocal.symm
          _ = hexInfra_midAccum hexAWStart 1 (base ++ [t, u]) :=
            (hexJordan_midAccum_append _ _ _ _).symm
          _ = hexInfra_midAccum hexAWStart 1 ts := by rw [← hsplit']
          _ = hexAWMid c endEdge := hendMid
      exact hendNe.2 (hexAWMid_edge_injective c hmid).symm
    · simp only [List.length_cons] at hlt
      omega


theorem HexEndpointLocalCrossing.terminalBlock_sum_cases
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3)
    (hlen : 3 ≤ (ts.drop C.index).length) :
    (ts[C.index]'C.index_lt = 1 ∧
        ((ts.drop C.index).sum = -4 ∨ (ts.drop C.index).sum = 8)) ∨
      (ts[C.index]'C.index_lt = -1 ∧
        ((ts.drop C.index).sum = 4 ∨ (ts.drop C.index).sum = -8)) := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let h := hexInfra_headAccum 1 base
  let H := hexInfra_headAccum (h + t) tail
  let dirs := hexCSBrickDirections (h + t) tail
  have ht : t = 1 ∨ t = -1 :=
    hlegal.1 t (List.getElem_mem C.index_lt)
  have htail : ∀ u ∈ tail, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_drop hu)
  have hdrop : ts.drop C.index = t :: tail := by
    simpa only [t, tail] using List.drop_eq_getElem_cons C.index_lt
  have hlenDirs : 3 ≤ dirs.length := by
    simp only [dirs, hexCSBrickDirections_length]
    rw [hdrop] at hlen
    simpa using hlen
  letI : NeZero dirs.length := ⟨by omega⟩
  have hgeom := C.terminalBrick_closed_nodup
    hnotOutside hlegal endEdge hend hcount
  have hclosed : ons_pathDisplacement dirs = 0 := by
    simpa only [base, t, tail, h, dirs] using hgeom.1
  have hsimple : (ons_pathVertices dirs).dropLast.Nodup := by
    simpa only [base, t, tail, h, dirs] using hgeom.2
  have hturn := ons_cyclicTurnSum_eq_four_or_neg_four_of_simple_list
    dirs hclosed hsimple hlenDirs
  have hopen := hexCS_brick_open_telescope (h + t) tail htail
  have hclosing := C.closing_brick_identity
    hnotOutside hlegal endEdge hend hcount
  have hclosing' : 2 * (-t) + 3 * ons_turnPow
      (hexBrickDir (hexCSHeadingFin H))
      (hexBrickDir (hexCSHeadingFin (h + t))) =
    hexBrickTurnPotential (hexCSHeadingFin (h + t)) -
      hexBrickTurnPotential (hexCSHeadingFin H) := by
    simpa only [base, t, tail, h, H] using hclosing
  have hcyc : ons_cyclicTurnSum dirs = ons_openTurnSum dirs +
      ons_turnPow (hexBrickDir (hexCSHeadingFin H))
        (hexBrickDir (hexCSHeadingFin (h + t))) := by
    have hdne : dirs ≠ [] := by
      intro hd
      have := congrArg List.length hd
      simp [dirs] at this
    have hc := hexCS_cyclicTurnSum_eq_open_add_close dirs hdne
    simpa only [dirs, hexCSBrickDirections_getLast,
      hexCSBrickDirections_head] using hc
  have hbalance : 2 * (tail.sum - t) +
      3 * ons_cyclicTurnSum dirs = 0 := by
    rw [hcyc]
    linear_combination hopen + hclosing'
  rw [hdrop]
  rcases ht with ht | ht <;> rcases hturn with hfour | hnegfour
  all_goals simp only [List.sum_cons, ht] at hbalance ⊢ <;> omega


theorem HexEndpointLocalCrossing.terminalBlock_sum_cases_auto
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    (ts[C.index]'C.index_lt = 1 ∧
        ((ts.drop C.index).sum = -4 ∨ (ts.drop C.index).sum = 8)) ∨
      (ts[C.index]'C.index_lt = -1 ∧
        ((ts.drop C.index).sum = 4 ∨ (ts.drop C.index).sum = -8)) :=
  C.terminalBlock_sum_cases hnotOutside hlegal endEdge hend hcount
    (C.terminalBlock_length_ge_three
      hnotOutside hlegal endEdge hend hcount)


end
end StatMech.Universality
