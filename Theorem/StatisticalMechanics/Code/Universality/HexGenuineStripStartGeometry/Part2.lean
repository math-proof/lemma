/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Def.StatisticalMechanics.Code.Universality.HexGenuineStripStartGeometry.Part3


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


@[simp] theorem hexGenuineStripCoordinateRegion_start :
    hexGenuineStripCoordinateRegion.start = hexGenuineStripRegion.start := rfl

@[simp] theorem hexGenuineStrip_cls_A :
    hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain
      hexGenuineStripIncA = 0 := by
  rw [hexRegionClsInc, hexGenuineStrip_mid_A]
  exact hexRegionCls_start hexGenuineStripCoordinateRegion

@[simp] theorem hexGenuineStrip_cls_U :
    hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain
      hexGenuineStripIncU = 4 := by
  rw [hexRegionClsInc, hexGenuineStrip_mid_U,
    hexGenuineStrip_mid_U_eq_halfStep_zero]
  apply hexRegionCls_right
  · simp [hexGenuineStripCoordinateRegion]
  · intro h
    change halfStep 0 = hexGenuineStripStart at h
    apply hexConcrete_a_ne_q hexGenuineStripStart 1
    rw [hexGenuineStrip_mid_U_eq_halfStep_zero]
    exact h.symm
  · simp

@[simp] theorem hexGenuineStrip_cls_Tp :
    hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain
      hexGenuineStripIncTp = 2 := by
  rw [hexRegionClsInc, hexGenuineStrip_mid_Tp,
    hexGenuineStrip_mid_Tp_eq_halfStep_two]
  apply hexRegionCls_topslant
  · simp [hexGenuineStripCoordinateRegion]
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  · intro h
    change halfStep 2 = hexGenuineStripStart at h
    apply hexConcrete_a_ne_r hexGenuineStripStart 1
    rw [hexGenuineStrip_mid_Tp_eq_halfStep_two]
    exact h.symm
  · simp
  · simp [hexGenuineStripCoordinateRegion]
    have hs : 0 < Real.sqrt 3 / 4 := by positivity
    linarith


theorem hexGenuineStrip_class_zero_iff_start
    (e : HexIncidence (Fin 1))
    (he : e ∈ hexGenuineStripDomain.incidences \
      hexGenuineStripPairing.interior) :
    hexRegionClsInc hexGenuineStripCoordinateRegion hexGenuineStripDomain e = 0
      ↔ hexGenuineStripDomain.mid e.vtx e.edge =
        hexGenuineStripRegion.start := by
  rw [hexGenuineStrip_boundaryIncidences] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · rw [hexGenuineStrip_cls_A, hexGenuineStrip_mid_A]
    simp [hexGenuineStripRegion, hexVBCRegion]
  · rw [hexGenuineStrip_cls_U, hexGenuineStrip_mid_U]
    constructor
    · intro h
      have : (4 : Fin 5) ≠ 0 := by decide
      exact (this h).elim
    · intro h
      exfalso
      apply hexConcrete_a_ne_q hexGenuineStripStart 1
      simpa [hexGenuineStripRegion, hexVBCRegion] using h.symm
  · rw [hexGenuineStrip_cls_Tp, hexGenuineStrip_mid_Tp]
    constructor
    · intro h
      have : (2 : Fin 5) ≠ 0 := by decide
      exact (this h).elim
    · intro h
      exfalso
      apply hexConcrete_a_ne_r hexGenuineStripStart 1
      simpa [hexGenuineStripRegion, hexVBCRegion] using h.symm

@[simp] theorem hexGenuineStrip_startFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 0) = {hexGenuineStripIncA} := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h4 : (4 : Fin 5) ≠ 0 := by decide
  have h2 : (2 : Fin 5) ≠ 0 := by decide
  simp [h4, h2]

@[simp] theorem hexGenuineStrip_LFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 1) = ∅ := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h0 : (0 : Fin 5) ≠ 1 := by decide
  have h4 : (4 : Fin 5) ≠ 1 := by decide
  have h2 : (2 : Fin 5) ≠ 1 := by decide
  simp [h0, h4, h2]

@[simp] theorem hexGenuineStrip_TpFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 2) = {hexGenuineStripIncTp} := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h0 : (0 : Fin 5) ≠ 2 := by decide
  have h4 : (4 : Fin 5) ≠ 2 := by decide
  simp [h0, h4]

@[simp] theorem hexGenuineStrip_TmFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 3) = ∅ := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h0 : (0 : Fin 5) ≠ 3 := by decide
  have h4 : (4 : Fin 5) ≠ 3 := by decide
  have h2 : (2 : Fin 5) ≠ 3 := by decide
  simp [h0, h4, h2]

@[simp] theorem hexGenuineStrip_UFiber :
    (hexGenuineStripDomain.incidences \
        hexGenuineStripPairing.interior).filter
      (fun e => hexRegionClsInc hexGenuineStripCoordinateRegion
        hexGenuineStripDomain e = 4) = {hexGenuineStripIncU} := by
  rw [hexGenuineStrip_boundaryIncidences]
  simp only [Finset.filter_insert, hexGenuineStrip_cls_A,
    hexGenuineStrip_cls_U, hexGenuineStrip_cls_Tp, Finset.filter_singleton]
  have h0 : (0 : Fin 5) ≠ 4 := by decide
  have h2 : (2 : Fin 5) ≠ 4 := by decide
  simp [h0, h2]


theorem hexGenuineStrip_mid_complete (m : ℂ)
    (hm : m ∈ hexGenuineStripRegion.mids) :
    ∃ e ∈ hexGenuineStripDomain.incidences \
      hexGenuineStripPairing.interior,
      hexGenuineStripDomain.mid e.vtx e.edge = m := by
  change m ∈
    ({hexGenuineStripStart, hexConcreteQ hexGenuineStripStart 1,
      hexConcreteR hexGenuineStripStart 1} : Finset ℂ) at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · refine ⟨hexGenuineStripIncA, ?_, hexGenuineStrip_mid_A⟩
    rw [hexGenuineStrip_boundaryIncidences]
    simp
  · refine ⟨hexGenuineStripIncU, ?_, hexGenuineStrip_mid_U⟩
    rw [hexGenuineStrip_boundaryIncidences]
    simp
  · refine ⟨hexGenuineStripIncTp, ?_, hexGenuineStrip_mid_Tp⟩
    rw [hexGenuineStrip_boundaryIncidences]
    simp


theorem hexGenuineStrip_boundary_mid_injective
    (e₁ : HexIncidence (Fin 1))
    (he₁ : e₁ ∈ hexGenuineStripDomain.incidences \
      hexGenuineStripPairing.interior)
    (e₂ : HexIncidence (Fin 1))
    (he₂ : e₂ ∈ hexGenuineStripDomain.incidences \
      hexGenuineStripPairing.interior)
    (hmid : hexGenuineStripDomain.mid e₁.vtx e₁.edge =
      hexGenuineStripDomain.mid e₂.vtx e₂.edge) :
    e₁ = e₂ := by
  rw [hexGenuineStrip_boundaryIncidences] at he₁ he₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at he₁ he₂
  rcases he₁ with rfl | rfl | rfl <;>
    rcases he₂ with rfl | rfl | rfl
  · rfl
  · exfalso
    rw [hexGenuineStrip_mid_A, hexGenuineStrip_mid_U] at hmid
    exact (hexConcrete_a_ne_q hexGenuineStripStart 1) hmid
  · exfalso
    rw [hexGenuineStrip_mid_A, hexGenuineStrip_mid_Tp] at hmid
    exact (hexConcrete_a_ne_r hexGenuineStripStart 1) hmid
  · exfalso
    rw [hexGenuineStrip_mid_U, hexGenuineStrip_mid_A] at hmid
    exact (hexConcrete_a_ne_q hexGenuineStripStart 1) hmid.symm
  · rfl
  · exfalso
    rw [hexGenuineStrip_mid_U, hexGenuineStrip_mid_Tp] at hmid
    exact (hexConcrete_q_ne_r hexGenuineStripStart 1) hmid
  · exfalso
    rw [hexGenuineStrip_mid_Tp, hexGenuineStrip_mid_A] at hmid
    exact (hexConcrete_a_ne_r hexGenuineStripStart 1) hmid.symm
  · exfalso
    rw [hexGenuineStrip_mid_Tp, hexGenuineStrip_mid_U] at hmid
    exact (hexConcrete_q_ne_r hexGenuineStripStart 1) hmid.symm
  · rfl


theorem hexGenuineStrip_existsUnique_boundary_incidence (m : ℂ)
    (hm : m ∈ hexGenuineStripRegion.mids) :
    ∃! e : HexIncidence (Fin 1),
      e ∈ hexGenuineStripDomain.incidences \
          hexGenuineStripPairing.interior
        ∧ hexGenuineStripDomain.mid e.vtx e.edge = m := by
  obtain ⟨e, he, hmid⟩ := hexGenuineStrip_mid_complete m hm
  refine ⟨e, ⟨he, hmid⟩, ?_⟩
  intro e' he'
  exact hexGenuineStrip_boundary_mid_injective e' he'.1 e he
    (he'.2.trans hmid.symm)


end StatMech.Universality
