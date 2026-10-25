/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
import Def.StatisticalMechanics.Code.Universality.HexStartPhaseRepair


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


theorem HexFiniteStripIncidenceEnumeration.exists_startIncidence
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) :
    ∃ eA : HexIncidence V,
      hexFiniteStripPhysicalStartFiber (R := R) P = {eA} := by
  obtain ⟨eA, heA, hmidA⟩ :=
    E.side_complete R.start R.start_mem (Or.inl rfl)
  refine ⟨eA, ?_⟩
  ext e
  simp only [hexFiniteStripPhysicalStartFiber, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨he, hmid⟩
    exact E.boundary_mid_injective e he eA heA (hmid.trans hmidA.symm)
  · rintro rfl
    exact ⟨heA, hmidA⟩


theorem HexFiniteStripIncidenceEnumeration.startFiber_card_eq_one
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) :
    (hexFiniteStripPhysicalStartFiber (R := R) P).card = 1 := by
  obtain ⟨eA, heA⟩ := E.exists_startIncidence
  rw [heA, Finset.card_singleton]


theorem HexFiniteStripIncidenceEnumeration.exists_classifiedStartIncidence
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) (G : HexRegion)
    (hclass : ∀ e ∈ D.incidences \ P.interior,
      hexRegionClsInc G D e = 0 ↔ D.mid e.vtx e.edge = R.start) :
    ∃ eA : HexIncidence V,
      (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0) = {eA} := by
  obtain ⟨eA, heA⟩ := E.exists_startIncidence
  refine ⟨eA, ?_⟩
  rw [← heA]
  ext e
  simp only [hexFiniteStripPhysicalStartFiber, Finset.mem_filter]
  constructor
  · rintro ⟨he, hzero⟩
    exact ⟨he, (hclass e he).mp hzero⟩
  · rintro ⟨he, hmid⟩
    exact ⟨he, (hclass e he).mpr hmid⟩


theorem HexFiniteStripIncidenceEnumeration.exists_classifiedStartData
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) (G : HexRegion)
    (hstart : G.start = R.start)
    (hclass : ∀ e ∈ D.incidences \ P.interior,
      hexRegionClsInc G D e = 0 ↔ D.mid e.vtx e.edge = R.start) :
    ∃ eA : HexIncidence V,
      (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0) = {eA}
        ∧ D.mid eA.vtx eA.edge = G.start := by
  obtain ⟨eA, hfiber⟩ := E.exists_classifiedStartIncidence G hclass
  have heA : eA ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0) := by
    rw [hfiber]
    simp
  have heBoundary : eA ∈ D.incidences \ P.interior :=
    (Finset.mem_filter.mp heA).1
  have hzero : hexRegionClsInc G D eA = 0 :=
    (Finset.mem_filter.mp heA).2
  refine ⟨eA, hfiber, ?_⟩
  exact ((hclass eA heBoundary).mp hzero).trans hstart.symm


theorem hexStart_hexUnit_four : hexUnit (4 : ℤ) = -Complex.I := by
  rw [hexPhase_hexUnit_normalForm]
  have htilt : hexPhase_sideTilt (4 : ℤ) = -Real.pi := by
    unfold hexPhase_sideTilt
    norm_num
    ring
  rw [htilt]
  simp


theorem hexUnitPhase_proj (h : ℤ) (cmag : ℝ) (fSum : ℂ)
    (hphase : fSum =
      Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ)) :
    hexUnit h * fSum = Complex.I * (cmag : ℂ) := by
  have hdouble : 2 * fSum =
      2 * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ) := by
    rw [hphase]
    ring
  have hp := hexPhase_proj h cmag (2 * fSum) hdouble
  calc
    hexUnit h * fSum = ((1 / 2 : ℂ) * hexUnit h) * (2 * fSum) := by ring
    _ = Complex.I * (cmag : ℂ) := hp


theorem hexUnitPhase_half_proj (h : ℤ) (coeff value : ℝ) (fSum : ℂ)
    (hphase : fSum =
      Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I)
        * ((coeff * value : ℝ) : ℂ)) :
    ((1 / 2 : ℂ) * hexUnit h) * fSum =
      Complex.I * ((coeff * (value / 2) : ℝ) : ℂ) := by
  have hp := hexUnitPhase_proj h (coeff * value) fSum hphase
  calc
    ((1 / 2 : ℂ) * hexUnit h) * fSum =
        (1 / 2 : ℂ) * (hexUnit h * fSum) := by ring
    _ = (1 / 2 : ℂ) * (Complex.I * ((coeff * value : ℝ) : ℂ)) := by rw [hp]
    _ = Complex.I * ((coeff * (value / 2) : ℝ) : ℂ) := by
      push_cast
      ring


end StatMech.Universality
