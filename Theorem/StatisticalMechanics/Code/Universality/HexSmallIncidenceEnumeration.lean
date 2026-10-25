/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


theorem hexVBC_contourFamily_singleton_q (a : ℂ) (h0 : ℤ) :
    hexContourFamily (hexVBCRegion a h0).inRegion a h0
        ({hexConcreteQ a h0} : Set ℂ) = {[-1]} := by
  ext ts
  constructor
  · rintro ⟨hlegal, hstay, z, hz, hend⟩
    have hzq : z = hexConcreteQ a h0 := by simpa using hz
    subst z
    rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
    · subst ts
      have hp : (ofTurns a h0 []).EndsAt a := by
        rw [HexWalk.EndsAt]
        exact trivialWalk_endMid a h0
      rw [HexWalk.EndsAt] at hp hend
      exact (hexConcrete_a_ne_q a h0 (hp.symm.trans hend)).elim
    · subst ts
      simp
    · subst ts
      have hr := hexConcrete_endsAt_r a h0
      rw [HexWalk.EndsAt] at hend hr
      exact (hexConcrete_q_ne_r a h0 (hend.symm.trans hr)).elim
  · intro hts
    have h : ts = [-1] := by simpa using hts
    subst ts
    refine ⟨hexConcrete_legalSAW_one a h0 (-1) (Or.inr rfl),
      hexVBC_staysIn_q a h0, hexConcreteQ a h0, by simp, ?_⟩
    exact hexConcrete_endsAt_q a h0


theorem hexVBC_contourFamily_singleton_r (a : ℂ) (h0 : ℤ) :
    hexContourFamily (hexVBCRegion a h0).inRegion a h0
        ({hexConcreteR a h0} : Set ℂ) = {[1]} := by
  ext ts
  constructor
  · rintro ⟨hlegal, hstay, z, hz, hend⟩
    have hzr : z = hexConcreteR a h0 := by simpa using hz
    subst z
    rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
    · subst ts
      have hp : (ofTurns a h0 []).EndsAt a := by
        rw [HexWalk.EndsAt]
        exact trivialWalk_endMid a h0
      rw [HexWalk.EndsAt] at hp hend
      exact (hexConcrete_a_ne_r a h0 (hp.symm.trans hend)).elim
    · subst ts
      have hq := hexConcrete_endsAt_q a h0
      rw [HexWalk.EndsAt] at hend hq
      exact (hexConcrete_q_ne_r a h0 (hq.symm.trans hend)).elim
    · subst ts
      simp
  · intro hts
    have h : ts = [1] := by simpa using hts
    subst ts
    refine ⟨hexConcrete_legalSAW_one a h0 1 (Or.inl rfl),
      hexVBC_staysIn_r a h0, hexConcreteR a h0, by simp, ?_⟩
    exact hexConcrete_endsAt_r a h0


theorem hexVBC_contourSum_singleton_q (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexContourSum (hexVBCRegion a h0).inRegion a h0
        ({hexConcreteQ a h0} : Set ℂ) x = x ^ 2 := by
  rw [hexContourSum, hexVBC_contourFamily_singleton_q]
  let wq : {ts : List ℤ // ts ∈ ({[-1]} : Set (List ℤ))} := ⟨[-1], by simp⟩
  rw [tsum_eq_single wq]
  · simp [wq, ofTurns, HexWalk.numVertices]
  · intro w hw
    exfalso
    apply hw
    apply Subtype.ext
    have hprop := w.property
    change w.val = [-1] at hprop
    exact hprop


theorem hexVBC_contourSum_singleton_r (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexContourSum (hexVBCRegion a h0).inRegion a h0
        ({hexConcreteR a h0} : Set ℂ) x = x ^ 2 := by
  rw [hexContourSum, hexVBC_contourFamily_singleton_r]
  let wr : {ts : List ℤ // ts ∈ ({[1]} : Set (List ℤ))} := ⟨[1], by simp⟩
  rw [tsum_eq_single wr]
  · simp [wr, ofTurns, HexWalk.numVertices]
  · intro w hw
    exfalso
    apply hw
    apply Subtype.ext
    have hprop := w.property
    change w.val = [1] at hprop
    exact hprop


end StatMech.Universality
