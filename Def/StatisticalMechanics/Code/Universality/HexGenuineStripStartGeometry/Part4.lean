/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripStartGeometry.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


noncomputable def hexGenuineStripSides : HexContourSides where
  bottom := ∅
  slantPlus := {hexConcreteR hexGenuineStripStart 1}
  slantMinus := ∅
  top := {hexConcreteQ hexGenuineStripStart 1}


noncomputable def hexGenuineStripBoundaryCore :
    HexFiniteStripBoundaryCore hexGenuineStripRegion 1
      hexGenuineStripDomain hexGenuineStripPairing where
  sides := hexGenuineStripSides
  interior_sub := hexUncond_interior_sub hexGenuineStripStart 1
  vertex_mem := by
    intro v hv
    have hv0 : v = 0 := Subsingleton.elim _ _
    subst v
    change hexConcreteV hexGenuineStripStart 1 ∈
      hexVBC_adjClosure hexGenuineStripStart 1
    unfold hexConcreteV hexVBC_adjClosure
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simpa using
      (hexVBC_star_mem hexGenuineStripStart (halfStep 1) 1 0 (Or.inl rfl))
  mid_mem := by
    intro e he
    rw [hexGenuineStrip_incidences] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [hexGenuineStrip_mid_A]
      exact hexGenuineStripRegion.start_mem
    · change hexConcreteQ hexGenuineStripStart 1 ∈
        hexGenuineStripRegion.mids
      simp [hexGenuineStripRegion, hexVBCRegion]
    · change hexConcreteR hexGenuineStripStart 1 ∈
        hexGenuineStripRegion.mids
      simp [hexGenuineStripRegion, hexVBCRegion]
  obs_eq := by intro z; rfl
  lam := hexContourLambda hexGenuineStripRegion.inRegion
    hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
  tau := hexContourTauPlus hexGenuineStripRegion.inRegion
      hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
    + hexContourTauMinus hexGenuineStripRegion.inRegion
      hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
  ups := hexContourUpsilon hexGenuineStripRegion.inRegion
    hexGenuineStripRegion.start 1 hexGenuineStripSides hexChi
  Fa := hexChi
  lam_eq := rfl
  tau_eq := rfl
  ups_eq := rfl
  Fa_eq := by
    change (hexChi : ℂ) = parafObservable
      hexGenuineStripRegion.inRegion hexGenuineStripStart 1
        hexGenuineStripStart (5 / 8) hexChi
    exact (hexVBC_start_observable_eq_hexChi hexGenuineStripStart 1).symm


noncomputable def hexGenuineStripIncidenceEnumeration
    (B : HexFiniteStripBoundaryData hexGenuineStripRegion 1
      hexGenuineStripDomain hexGenuineStripPairing)
    (hsides : B.sides = hexGenuineStripSides) :
    HexFiniteStripIncidenceEnumeration B where
  mid_complete := by
    intro m hm
    obtain ⟨e, he, hmid⟩ := hexGenuineStrip_mid_complete m hm
    exact ⟨e, (Finset.mem_sdiff.mp he).1, hmid⟩
  boundary_mid_injective := hexGenuineStrip_boundary_mid_injective
  boundary_classified := by
    intro e he
    rw [hexGenuineStrip_boundaryIncidences] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · left
      simpa [hexGenuineStripRegion, hexVBCRegion] using hexGenuineStrip_mid_A
    · right; right; right; right
      rw [hexGenuineStrip_mid_U, hsides]
      simp [hexGenuineStripSides]
    · right; right; left
      rw [hexGenuineStrip_mid_Tp, hsides]
      simp [hexGenuineStripSides]
  part_unique := by
    intro z hz k l hk hl
    change z ∈
      ({hexGenuineStripStart, hexConcreteQ hexGenuineStripStart 1,
        hexConcreteR hexGenuineStripStart 1} : Finset ℂ) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have haq := hexConcrete_a_ne_q hexGenuineStripStart 1
    have har := hexConcrete_a_ne_r hexGenuineStripStart 1
    have hqr := hexConcrete_q_ne_r hexGenuineStripStart 1
    have haq4 : halfStep 4 ≠ hexConcreteQ (halfStep 4) 1 := by
      simpa using haq
    have har4 : halfStep 4 ≠ hexConcreteR (halfStep 4) 1 := by
      simpa using har
    have hqr4 : hexConcreteQ (halfStep 4) 1 ≠
        hexConcreteR (halfStep 4) 1 := by
      simpa using hqr
    have hqa4 := haq4.symm
    have hra4 := har4.symm
    have hrq4 := hqr4.symm
    rcases hz with rfl | rfl | rfl <;> fin_cases k <;> fin_cases l <;>
      simp [hexFiniteStripContourPart, hsides, hexGenuineStripSides,
        hexGenuineStripRegion, hexVBCRegion, haq4, har4, hqr4,
        hqa4, hra4, hrq4] at hk hl ⊢
  side_complete := by
    intro z hz _
    exact hexGenuineStrip_mid_complete z hz


noncomputable def hexGenuineStripFourPhaseData
    (phaseL :
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 1),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
        Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
          * ((hexBdryCl * hexGenuineStripBoundaryCore.lam : ℝ) : ℂ))
    (phaseTp :
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 2),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
        Complex.exp ((hexPhase_sideTilt (2 : ℤ) : ℝ) * Complex.I)
          * ((hexBdryCt * hexGenuineStripBoundaryCore.tau : ℝ) : ℂ))
    (phaseTm :
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 3),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
        Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
          * ((hexBdryCt * (0 : ℝ) : ℝ) : ℂ))
    (phaseU :
      (∑ e ∈ (hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior).filter
            (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
              hexGenuineStripDomain e = 4),
        hexGenuineStripDomain.obs
          (hexGenuineStripDomain.mid e.vtx e.edge)) =
        Complex.exp ((hexPhase_sideTilt (0 : ℤ) : ℝ) * Complex.I)
          * ((hexGenuineStripBoundaryCore.ups : ℝ) : ℂ)) :
    HexFiniteStripFourPhaseData hexGenuineStripBoundaryCore
      hexGenuineStripCoordinateRegion where
  start_eq := rfl
  heading := hexGenuineStripHeading
  hgeom := hexGenuineStrip_hgeom
  startIncidence := hexGenuineStripIncA
  startFiber_singleton := hexGenuineStrip_startFiber
  start_mid := by
    simpa [hexGenuineStripCoordinateRegion] using hexGenuineStrip_mid_A
  start_heading := rfl
  headL := 0
  headTp := 2
  headTm := 0
  headU := 0
  hHeadL := by
    intro e he
    rw [hexGenuineStrip_LFiber] at he
    simp at he
  hHeadTp := by
    intro e he
    rw [hexGenuineStrip_TpFiber] at he
    have heq := Finset.mem_singleton.mp he
    subst e
    rfl
  hHeadTm := by
    intro e he
    rw [hexGenuineStrip_TmFiber] at he
    simp at he
  hHeadU := by
    intro e he
    rw [hexGenuineStrip_UFiber] at he
    have heq := Finset.mem_singleton.mp he
    subst e
    rfl
  taup := hexGenuineStripBoundaryCore.tau
  taum := 0
  tau_eq := by ring
  phaseL := phaseL
  phaseTp := phaseTp
  phaseTm := phaseTm
  phaseU := phaseU

end StatMech.Universality
