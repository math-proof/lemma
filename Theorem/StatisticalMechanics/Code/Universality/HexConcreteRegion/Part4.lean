/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
import Def.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexConcrete_verts_card (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    (hexConcrete_region a h0 hclosure).verts.card = 3 := by
  obtain ⟨h1, h2, h3⟩ := hexConcrete_verts_distinct a h0
  show ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ).card = 3
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
    Finset.card_insert_of_notMem (by simp [h3]), Finset.card_singleton]


theorem hexConcrete_inRegion_iff (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (z : ℂ) :
    (hexConcrete_region a h0 hclosure).inRegion z
      ↔ (z = a ∨ z = hexConcreteQ a h0 ∨ z = hexConcreteR a h0) := by
  unfold HexFiniteRegion.inRegion hexConcrete_region
  simp [Finset.mem_insert]


theorem hexConcrete_staysIn_p (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    (ofTurns a h0 []).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
  intro m hm
  rw [hexConcrete_inRegion_iff]
  have : (ofTurns a h0 []).mids = [a] := by
    show (trivialWalk a h0).mids = [a]
    unfold HexWalk.mids; simp [trivialWalk]
  rw [this] at hm
  simp only [List.mem_singleton] at hm
  exact Or.inl hm


theorem hexConcrete_staysIn_q (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    (ofTurns a h0 [-1]).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
  intro m hm
  rw [hexConcrete_inRegion_iff]
  rw [hexConcrete_mids_qext] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)


theorem hexConcrete_staysIn_r (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    (ofTurns a h0 [1]).StaysIn (hexConcrete_region a h0 hclosure).inRegion := by
  intro m hm
  rw [hexConcrete_inRegion_iff]
  rw [hexConcrete_mids_rext] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)


theorem hexConcrete_support_classify (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexConcrete_region a h0 hclosure).inRegion) :
    ts = [] ∨ ts = [-1] ∨ ts = [1] := by
  
  have hlt : ts.length < 3 := by
    have := (hexConcrete_region a h0 hclosure).length_lt a h0 ts hlegal.2 hstay
    rwa [hexConcrete_verts_card a h0 hclosure] at this
  
  have hturns : ∀ t ∈ ts, t = 1 ∨ t = -1 := hlegal.1
  
  interval_cases hlen : ts.length
  · exact Or.inl (List.length_eq_zero_iff.mp hlen)
  · 
    obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
      match ts, hlen with
      | [t], _ => exact ⟨t, rfl⟩
    have ht : t = 1 ∨ t = -1 := hturns t (by simp)
    rcases ht with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  · 
    exfalso
    obtain ⟨t1, t2, rfl⟩ : ∃ t1 t2, ts = [t1, t2] := by
      match ts, hlen with
      | [t1, t2], _ => exact ⟨t1, t2, rfl⟩
    have ht1 : t1 = 1 ∨ t1 = -1 := hturns t1 (by simp)
    have ht2 : t2 = 1 ∨ t2 = -1 := hturns t2 (by simp)
    
    have hmem : (ofTurns a h0 [t1, t2]).endMid ∈ (ofTurns a h0 [t1, t2]).mids := by
      unfold HexWalk.endMid; exact List.getLast_mem _
    have hreg := hstay _ hmem
    rw [hexConcrete_inRegion_iff] at hreg
    obtain ⟨hna, hnq, hnr⟩ := hexConcrete_len2_endMid_not_mid a h0 t1 t2 ht1 ht2
    rcases hreg with h | h | h
    · exact hna h
    · exact hnq h
    · exact hnr h


theorem hexConcrete_covering_p (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hp : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0)) :
    ts = [] := by
  obtain ⟨hlegal, hstay⟩ :=
    (hexConcrete_region a h0 hclosure).support_isLegalSAW_staysIn
      (hexConcreteDu_ne a h0) ts hsupp
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · exact h
  · 
    exfalso
    rw [h] at hp
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hp hq
    rw [hexConcrete_p_eq] at hp
    exact hexConcrete_a_ne_q a h0 (hp.symm.trans hq)
  · exfalso
    rw [h] at hp
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hp hr
    rw [hexConcrete_p_eq] at hp
    exact hexConcrete_a_ne_r a h0 (hp.symm.trans hr)


theorem hexConcrete_covering_q (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hq : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) :
    ts = [-1] := by
  obtain ⟨hlegal, hstay⟩ :=
    (hexConcrete_region a h0 hclosure).support_isLegalSAW_staysIn
      (hexConcreteDu_ne a h0) ts hsupp
  have hqdef : hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 = hexConcreteQ a h0 := rfl
  rw [hqdef] at hq
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · exfalso
    rw [h] at hq
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]
      show (trivialWalk a h0).endMid = a
      exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hq hpe
    exact hexConcrete_a_ne_q a h0 (hpe.symm.trans hq)
  · exact h
  · exfalso
    rw [h] at hq
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hq hr
    exact hexConcrete_q_ne_r a h0 (hq.symm.trans hr)


theorem hexConcrete_covering_r (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hr : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0)) :
    ts = [1] := by
  obtain ⟨hlegal, hstay⟩ :=
    (hexConcrete_region a h0 hclosure).support_isLegalSAW_staysIn
      (hexConcreteDu_ne a h0) ts hsupp
  have hrdef : hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 = hexConcreteR a h0 := rfl
  rw [hrdef] at hr
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · exfalso
    rw [h] at hr
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]
      show (trivialWalk a h0).endMid = a
      exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hr hpe
    exact hexConcrete_a_ne_r a h0 (hpe.symm.trans hr)
  · exfalso
    rw [h] at hr
    have hqe := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hr hqe
    exact hexConcrete_q_ne_r a h0 (hqe.symm.trans hr)
  · exact h


theorem hexConcrete_paraf_guard (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (z : ℂ) (ts : List ℤ)
    (hne : parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0 z (5/8) hexChi ts ≠ 0) :
    (ofTurns a h0 ts).IsLegalSAW
      ∧ (ofTurns a h0 ts).StaysIn (hexConcrete_region a h0 hclosure).inRegion
      ∧ (ofTurns a h0 ts).EndsAt z := by
  by_contra hcon
  apply hne
  unfold parafSummand
  rw [if_neg hcon]


theorem hexConcrete_obs_p (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi [] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexConcrete_paraf_guard a h0 hclosure _ ts hne
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · exact hts h
  · rw [h] at hend
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hend hq; rw [hexConcrete_p_eq] at hend
    exact hexConcrete_a_ne_q a h0 (hend.symm.trans hq)
  · rw [h] at hend
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hend hr; rw [hexConcrete_p_eq] at hend
    exact hexConcrete_a_ne_r a h0 (hend.symm.trans hr)


theorem hexConcrete_obs_q (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi [-1] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexConcrete_paraf_guard a h0 hclosure _ ts hne
  have hqdef : hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 = hexConcreteQ a h0 := rfl
  rw [hqdef] at hend
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · rw [h] at hend
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hend hpe
    exact hexConcrete_a_ne_q a h0 (hpe.symm.trans hend)
  · exact hts h
  · rw [h] at hend
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hend hr
    exact hexConcrete_q_ne_r a h0 (hend.symm.trans hr)


theorem hexConcrete_obs_r (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0
        (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi [1] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexConcrete_paraf_guard a h0 hclosure _ ts hne
  have hrdef : hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 = hexConcreteR a h0 := rfl
  rw [hrdef] at hend
  rcases hexConcrete_support_classify a h0 hclosure ts hlegal hstay with h | h | h
  · rw [h] at hend
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hend hpe
    exact hexConcrete_a_ne_r a h0 (hpe.symm.trans hend)
  · rw [h] at hend
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hend hq
    exact hexConcrete_q_ne_r a h0 (hq.symm.trans hend)
  · exact hts h


theorem hexConcrete_summable (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ))
    (z : ℂ) :
    Summable fun ts =>
      parafSummand (hexConcrete_region a h0 hclosure).inRegion a h0 z (5/8) hexChi ts := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (s := {ts : List ℤ | ts = [] ∨ ts = [-1] ∨ ts = [1]} )
  · have : {ts : List ℤ | ts = [] ∨ ts = [-1] ∨ ts = [1]}
        = ({[], [-1], [1]} : Finset (List ℤ)) := by
      ext ts; simp
    rw [this]; exact (Finset.finite_toSet _)
  · intro ts hts
    simp only [Function.mem_support] at hts
    obtain ⟨hlegal, hstay, _⟩ := hexConcrete_paraf_guard a h0 hclosure z ts hts
    exact hexConcrete_support_classify a h0 hclosure ts hlegal hstay


end StatMech.Universality
