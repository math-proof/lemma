/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Structure.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction


namespace StatMech.Universality

open Complex HexWalk Set


theorem hexEmptyIncidenceBoundaryData_not_enumerated
    (R : HexFiniteRegion) (h0 : ℤ) :
    ¬ Nonempty (HexFiniteStripIncidenceEnumeration
      (hexEmptyIncidenceBoundaryData R h0)) := by
  rintro ⟨E⟩
  obtain ⟨e, he, _⟩ := E.mid_complete R.start R.start_mem
  rw [hexEmptyIncidenceDomain_incidences] at he
  simp at he


theorem HexPhaseData.startFiber_nonempty_of_Fa_ne_zero
    {V : Type*} [DecidableEq V]
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (H : HexPhaseData D P G) (hFa : H.Fa ≠ 0) :
    ((D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0)).Nonempty := by
  by_contra hempty
  have hfiber : (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hphase := H.phaseA
  rw [hfiber] at hphase
  simp only [Finset.sum_empty] at hphase
  have hreal : (-1 : ℝ) * H.Fa ≠ 0 := mul_ne_zero (by norm_num) hFa
  have hrhs : 2 * Complex.exp
        ((hexPhase_sideTilt H.headA : ℝ) * Complex.I)
      * (((-1 : ℝ) * H.Fa : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr hreal)
  exact hrhs hphase.symm


theorem HexPhaseData.Fa_eq_zero_of_startFiber_singleton
    {V : Type*} [DecidableEq V]
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (H : HexPhaseData D P G) (eA : HexIncidence V)
    (hfiber :
      (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0) = {eA})
    (hmid : D.mid eA.vtx eA.edge = G.start)
    (hobs : D.obs G.start = (H.Fa : ℂ)) :
    H.Fa = 0 := by
  have hphase := H.phaseA
  rw [hfiber, Finset.sum_singleton, hmid, hobs] at hphase
  have hnorm := congrArg norm hphase
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, norm_neg, abs_one, one_mul,
    mul_one] at hnorm
  have habs : |H.Fa| = 0 := by
    nlinarith [abs_nonneg H.Fa]
  exact abs_eq_zero.mp habs


theorem HexPhaseData.not_startFiber_singleton_of_Fa_eq_hexChi
    {V : Type*} [DecidableEq V]
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (H : HexPhaseData D P G) (eA : HexIncidence V)
    (hfiber :
      (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0) = {eA})
    (hmid : D.mid eA.vtx eA.edge = G.start)
    (hobs : D.obs G.start = (H.Fa : ℂ))
    (hFa : H.Fa = hexChi) : False := by
  have hzero := H.Fa_eq_zero_of_startFiber_singleton eA hfiber hmid hobs
  rw [hFa] at hzero
  exact (ne_of_gt hexChi_pos) hzero


theorem HexFiniteStripBoundaryData.phaseA_startFiber_card_ne_one
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ}
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (B : HexFiniteStripBoundaryData R h0 D P)
    (H : HexPhaseData D P G)
    (hstart : G.start = R.start)
    (hFa : H.Fa = B.Fa)
    (hmid : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0),
      D.mid e.vtx e.edge = G.start) :
    ((D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0)).card ≠ 1 := by
  intro hcard
  obtain ⟨eA, hfiber⟩ := Finset.card_eq_one.mp hcard
  have heA : eA ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0) := by
    rw [hfiber]
    simp
  have hobs : D.obs G.start = (H.Fa : ℂ) := by
    calc
      D.obs G.start = D.obs R.start := by rw [hstart]
      _ = (B.Fa : ℂ) := B.Fa_eq.symm
      _ = (H.Fa : ℂ) := by rw [hFa]
  exact H.not_startFiber_singleton_of_Fa_eq_hexChi eA hfiber
    (hmid eA heA) hobs (hFa.trans B.Fa_eq_hexChi)


theorem HexFiniteStripBoundaryData.two_le_phaseA_startFiber_card
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ}
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (B : HexFiniteStripBoundaryData R h0 D P)
    (H : HexPhaseData D P G)
    (hstart : G.start = R.start)
    (hFa : H.Fa = B.Fa)
    (hmid : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0),
      D.mid e.vtx e.edge = G.start) :
    2 ≤ ((D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0)).card := by
  have hFa0 : H.Fa ≠ 0 := by
    rw [hFa, B.Fa_eq_hexChi]
    exact ne_of_gt hexChi_pos
  have hpos : 0 < ((D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0)).card :=
    Finset.card_pos.mpr (H.startFiber_nonempty_of_Fa_ne_zero hFa0)
  have hone := B.phaseA_startFiber_card_ne_one H hstart hFa hmid
  omega

end StatMech.Universality
