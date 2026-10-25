/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBoundConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexVBC_inRegion_iff (a : ℂ) (h0 : ℤ) (z : ℂ) :
    (hexVBCRegion a h0).inRegion z ↔ (z = a ∨ z = hexConcreteQ a h0 ∨ z = hexConcreteR a h0) := by
  unfold HexFiniteRegion.inRegion hexVBCRegion
  simp [Finset.mem_insert]


theorem hexVBC_region_stay_short (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hturns : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hstay : ∀ m ∈ (ofTurns a h0 ts).mids,
      m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) :
    ts.length ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hcon' : 2 ≤ ts.length := hcon
  match ts, hcon' with
  | t1 :: t2 :: rest, _ =>
    have ht1 : t1 = 1 ∨ t1 = -1 := hturns t1 (by simp)
    have ht2 : t2 = 1 ∨ t2 = -1 := hturns t2 (by simp)
    have hm2mem : (ofTurns a h0 [t1, t2]).endMid ∈ (ofTurns a h0 (t1 :: t2 :: rest)).mids := by
      rw [hexConcrete_endMid_two]
      show a + halfStep h0 + halfStep (h0 + t1) + halfStep (h0 + t1) + halfStep (h0 + t1 + t2)
        ∈ midsAux a h0 (t1 :: t2 :: rest)
      rw [midsAux_cons, midsAux_cons]
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      rw [show a + halfStep h0 + halfStep (h0 + t1) + halfStep (h0 + t1) + halfStep (h0 + t1 + t2)
          = (a + halfStep h0 + halfStep (h0 + t1)) + halfStep (h0 + t1) + halfStep (h0 + t1 + t2) by
        ring]
      cases rest with
      | nil => simp [midsAux]
      | cons s ss => rw [midsAux_cons]; exact List.mem_cons_self
    have hreg := hstay _ hm2mem
    obtain ⟨hna, hnq, hnr⟩ := hexConcrete_len2_endMid_not_mid a h0 t1 t2 ht1 ht2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hreg
    rcases hreg with h | h | h
    · exact hna h
    · exact hnq h
    · exact hnr h


theorem hexVBC_support_classify (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexVBCRegion a h0).inRegion) :
    ts = [] ∨ ts = [-1] ∨ ts = [1] := by
  have hstay' : ∀ m ∈ (ofTurns a h0 ts).mids,
      m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) := by
    intro m hm
    have := hstay m hm
    rw [hexVBC_inRegion_iff] at this
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact this
  have hlen : ts.length ≤ 1 := hexVBC_region_stay_short a h0 ts hlegal.1 hstay'
  interval_cases hl : ts.length
  · exact Or.inl (List.length_eq_zero_iff.mp hl)
  · obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
      match ts, hl with
      | [t], _ => exact ⟨t, rfl⟩
    rcases hlegal.1 t (by simp) with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)


theorem hexVBC_staysIn_p (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 []).StaysIn (hexVBCRegion a h0).inRegion := by
  intro m hm
  rw [hexVBC_inRegion_iff]
  have : (ofTurns a h0 []).mids = [a] := by
    show (trivialWalk a h0).mids = [a]; unfold HexWalk.mids; simp [trivialWalk]
  rw [this] at hm
  simp only [List.mem_singleton] at hm
  exact Or.inl hm


theorem hexVBC_staysIn_q (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1]).StaysIn (hexVBCRegion a h0).inRegion := by
  intro m hm
  rw [hexVBC_inRegion_iff, hexConcrete_mids_qext] at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)


theorem hexVBC_staysIn_r (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1]).StaysIn (hexVBCRegion a h0).inRegion := by
  intro m hm
  rw [hexVBC_inRegion_iff, hexConcrete_mids_rext] at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)


theorem hexVBC_support_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0))) :
    (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn (hexVBCRegion a h0).inRegion :=
  (hexVBCRegion a h0).support_isLegalSAW_staysIn (hexConcreteDu_ne a h0) ts hsupp


theorem hexVBC_covering_p (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hp : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0)) :
    ts = [] := by
  obtain ⟨hlegal, hstay⟩ := hexVBC_support_legal a h0 ts hsupp
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · exact h
  · exfalso; rw [h] at hp
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hp hq; rw [hexConcrete_p_eq] at hp
    exact hexConcrete_a_ne_q a h0 (hp.symm.trans hq)
  · exfalso; rw [h] at hp
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hp hr; rw [hexConcrete_p_eq] at hp
    exact hexConcrete_a_ne_r a h0 (hp.symm.trans hr)


theorem hexVBC_covering_q (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hq : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) :
    ts = [-1] := by
  obtain ⟨hlegal, hstay⟩ := hexVBC_support_legal a h0 ts hsupp
  have hqdef : hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 = hexConcreteQ a h0 := rfl
  rw [hqdef] at hq
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · exfalso; rw [h] at hq
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hq hpe
    exact hexConcrete_a_ne_q a h0 (hpe.symm.trans hq)
  · exact h
  · exfalso; rw [h] at hq
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hq hr
    exact hexConcrete_q_ne_r a h0 (hq.symm.trans hr)


theorem hexVBC_covering_r (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hr : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0)) :
    ts = [1] := by
  obtain ⟨hlegal, hstay⟩ := hexVBC_support_legal a h0 ts hsupp
  have hrdef : hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 = hexConcreteR a h0 := rfl
  rw [hrdef] at hr
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · exfalso; rw [h] at hr
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hr hpe
    exact hexConcrete_a_ne_r a h0 (hpe.symm.trans hr)
  · exfalso; rw [h] at hr
    have hqe := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hr hqe
    exact hexConcrete_q_ne_r a h0 (hqe.symm.trans hr)
  · exact h


theorem hexVBC_paraf_guard (a : ℂ) (h0 : ℤ) (z : ℂ) (ts : List ℤ)
    (hne : parafSummand (hexVBCRegion a h0).inRegion a h0 z (5/8) hexChi ts ≠ 0) :
    (ofTurns a h0 ts).IsLegalSAW
      ∧ (ofTurns a h0 ts).StaysIn (hexVBCRegion a h0).inRegion
      ∧ (ofTurns a h0 ts).EndsAt z := by
  by_contra hcon
  apply hne; unfold parafSummand; rw [if_neg hcon]


theorem hexVBC_summable (a : ℂ) (h0 : ℤ) (z : ℂ) :
    Summable fun ts => parafSummand (hexVBCRegion a h0).inRegion a h0 z (5/8) hexChi ts := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (s := {ts : List ℤ | ts = [] ∨ ts = [-1] ∨ ts = [1]})
  · have : {ts : List ℤ | ts = [] ∨ ts = [-1] ∨ ts = [1]} = ({[], [-1], [1]} : Finset (List ℤ)) := by
      ext ts; simp
    rw [this]; exact Finset.finite_toSet _
  · intro ts hts
    simp only [Function.mem_support] at hts
    obtain ⟨hlegal, hstay, _⟩ := hexVBC_paraf_guard a h0 z ts hts
    exact hexVBC_support_classify a h0 ts hlegal hstay


theorem hexVBC_obs_p (a : ℂ) (h0 : ℤ) :
    parafObservable (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi [] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexVBC_paraf_guard a h0 _ ts hne
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · exact hts h
  · rw [h] at hend
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hend hq; rw [hexConcrete_p_eq] at hend
    exact hexConcrete_a_ne_q a h0 (hend.symm.trans hq)
  · rw [h] at hend
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hend hr; rw [hexConcrete_p_eq] at hend
    exact hexConcrete_a_ne_r a h0 (hend.symm.trans hr)


theorem hexVBC_obs_q (a : ℂ) (h0 : ℤ) :
    parafObservable (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi [-1] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexVBC_paraf_guard a h0 _ ts hne
  have hqdef : hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 = hexConcreteQ a h0 := rfl
  rw [hqdef] at hend
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
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


theorem hexVBC_obs_r (a : ℂ) (h0 : ℤ) :
    parafObservable (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi [1] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexVBC_paraf_guard a h0 _ ts hne
  have hrdef : hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 = hexConcreteR a h0 := rfl
  rw [hrdef] at hend
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
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


theorem hexVBC_vertex_relation_unconditional (a : ℂ) (h0 : ℤ) :
    ((hexConcreteV a h0 + hexConcreteDu a h0) - hexConcreteV a h0)
        * parafObservable (hexVBCRegion a h0).inRegion a h0
            (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi
      + ((hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) - hexConcreteV a h0)
          * parafObservable (hexVBCRegion a h0).inRegion a h0
              (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi
      + ((hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) - hexConcreteV a h0)
          * parafObservable (hexVBCRegion a h0).inRegion a h0
              (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi = 0 := by
  refine hexClass_vertex_relation_singleTriplet (hexVBCRegion a h0).inRegion a h0
    (hexConcreteV a h0) (hexConcreteDu a h0) [] (hexConcreteDu_ne a h0)
    (hexVBC_summable a h0 _) (hexVBC_summable a h0 _) (hexVBC_summable a h0 _)
    ⟨(hexConcrete_atoms a h0).1.1, hexVBC_staysIn_p a h0, (hexConcrete_atoms a h0).1.2⟩
    (by simpa using ⟨(hexConcrete_atoms a h0).2.1.1, hexVBC_staysIn_q a h0,
        (hexConcrete_atoms a h0).2.1.2⟩)
    (by simpa using ⟨(hexConcrete_atoms a h0).2.2.1.1, hexVBC_staysIn_r a h0,
        (hexConcrete_atoms a h0).2.2.1.2⟩)
    (by simpa using (hexConcrete_atoms a h0).2.2.2.1)
    (by simpa using (hexConcrete_atoms a h0).2.2.2.2)
    ?_ ?_ ?_ ?_
  · intro ts hts hp
    exact (hexVBC_covering_p a h0 ts hts hp).symm
  · intro ts hts hq
    have := hexVBC_covering_q a h0 ts hts (by simpa using hq)
    simpa using this.symm
  · intro ts hts hr
    have := hexVBC_covering_r a h0 ts hts (by simpa using hr)
    simpa using this.symm
  · rw [hexVBC_obs_p a h0, hexVBC_obs_q a h0, hexVBC_obs_r a h0]; simp

end StatMech.Universality
