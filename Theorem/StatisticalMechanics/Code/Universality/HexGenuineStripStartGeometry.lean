/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Def.StatisticalMechanics.Code.Universality.HexGenuineStripStartGeometry.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


@[simp] theorem hexGenuineStrip_vertex_eq_zero (v : Fin 1) : v = 0 :=
  Subsingleton.elim _ _

@[simp] theorem hexGenuineStrip_incidences :
    hexGenuineStripDomain.incidences =
      {hexGenuineStripIncA, hexGenuineStripIncU, hexGenuineStripIncTp} := by
  ext e
  rcases e with ⟨v, j⟩
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  fin_cases j <;>
    simp [HexDomain.incidences, hexGenuineStripDomain,
      hexUncondDomain, hexGenuineStripIncA, hexGenuineStripIncU,
      hexGenuineStripIncTp]

@[simp] theorem hexGenuineStrip_boundaryIncidences :
    hexGenuineStripDomain.incidences \ hexGenuineStripPairing.interior =
      {hexGenuineStripIncA, hexGenuineStripIncU, hexGenuineStripIncTp} := by
  rw [hexGenuineStrip_incidences]
  rfl

@[simp] theorem hexGenuineStrip_mid_A :
    hexGenuineStripDomain.mid hexGenuineStripIncA.vtx
        hexGenuineStripIncA.edge = hexGenuineStripStart := by
  simp [hexGenuineStripDomain, hexUncondDomain, hexUncondMid,
    hexGenuineStripIncA, hexGenuineStripStart, hexConcreteV,
    hexConcreteDu]

@[simp] theorem hexGenuineStrip_mid_U :
    hexGenuineStripDomain.mid hexGenuineStripIncU.vtx
        hexGenuineStripIncU.edge = hexConcreteQ hexGenuineStripStart 1 := rfl

@[simp] theorem hexGenuineStrip_mid_Tp :
    hexGenuineStripDomain.mid hexGenuineStripIncTp.vtx
        hexGenuineStripIncTp.edge = hexConcreteR hexGenuineStripStart 1 := rfl


theorem hexGenuineStrip_hgeom (v : Fin 1) (j : Fin 3) :
    hexGenuineStripDomain.mid v j - hexGenuineStripDomain.pos v =
      (1 / 2 : ℂ) * hexUnit (hexGenuineStripHeading v j) := by
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  fin_cases j
  · simp [hexGenuineStripDomain, hexUncondDomain, hexUncondMid,
      hexGenuineStripHeading, hexConcreteDu, halfStep]
    rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
    ring
  · simp [hexGenuineStripDomain, hexUncondDomain, hexUncondMid,
      hexGenuineStripHeading, hexConcreteDu, halfStep]
    have h4 : hexUnit (4 : ℤ) = -hexUnit 1 := by
      simpa using hexUnit_add_three 1
    have h6 : hexUnit (0 : ℤ) = hexOmega * hexUnit 4 := by
      calc
        hexUnit (0 : ℤ) = hexUnit (0 + 6) := (hexUnit_add_six 0).symm
        _ = hexUnit (4 + 2) := by norm_num
        _ = hexOmega * hexUnit 4 := hexUnit_add_two 4
    rw [h6, h4]
    ring
  · simp [hexGenuineStripDomain, hexUncondDomain, hexUncondMid,
      hexGenuineStripHeading, hexConcreteDu, halfStep]
    have h4 : hexUnit (4 : ℤ) = -hexUnit 1 := by
      simpa using hexUnit_add_three 1
    have h8 : hexUnit (2 : ℤ) = hexOmega ^ 2 * hexUnit 4 := by
      calc
        hexUnit (2 : ℤ) = hexUnit (2 + 6) := (hexUnit_add_six 2).symm
        _ = hexUnit (4 + 4) := by norm_num
        _ = hexOmega ^ 2 * hexUnit 4 := hexUnit_add_four 4
    rw [h8, h4]
    ring

@[simp] theorem hexGenuineStrip_start_eq_halfStep_four :
    hexGenuineStripStart = halfStep 4 := by
  unfold hexGenuineStripStart halfStep
  rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
  ring

@[simp] theorem hexGenuineStrip_mid_U_eq_halfStep_zero :
    hexConcreteQ hexGenuineStripStart 1 = halfStep 0 := by
  have hpos : hexGenuineStripDomain.pos (0 : Fin 1) = 0 := by
    change hexConcreteV hexGenuineStripStart 1 = 0
    unfold hexConcreteV hexGenuineStripStart
    ring
  have h := hexGenuineStrip_hgeom (0 : Fin 1) (1 : Fin 3)
  rw [hpos, sub_zero] at h
  change hexConcreteQ hexGenuineStripStart 1 = (1 / 2 : ℂ) * hexUnit 0 at h
  simpa [halfStep] using h

@[simp] theorem hexGenuineStrip_mid_Tp_eq_halfStep_two :
    hexConcreteR hexGenuineStripStart 1 = halfStep 2 := by
  have hpos : hexGenuineStripDomain.pos (0 : Fin 1) = 0 := by
    change hexConcreteV hexGenuineStripStart 1 = 0
    unfold hexConcreteV hexGenuineStripStart
    ring
  have h := hexGenuineStrip_hgeom (0 : Fin 1) (2 : Fin 3)
  rw [hpos, sub_zero] at h
  change hexConcreteR hexGenuineStripStart 1 = (1 / 2 : ℂ) * hexUnit 2 at h
  simpa [halfStep] using h

@[simp] theorem hexGenuineStrip_halfStep_zero_re :
    (halfStep 0).re = Real.sqrt 3 / 4 := by
  simpa [hexCell, halfStep] using hexCell_mid_zero_re (0 : ℂ)

@[simp] theorem hexGenuineStrip_halfStep_two_re :
    (halfStep 2).re = -(Real.sqrt 3 / 4) := by
  unfold halfStep
  have e2 : hexUnit (2 : ℤ) =
      Complex.exp (((5 * Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
    unfold hexUnit
    congr 1
    push_cast
    ring
  rw [e2, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_six]
  simp
  ring

@[simp] theorem hexGenuineStrip_halfStep_two_im :
    (halfStep 2).im = 1 / 4 := by
  unfold halfStep
  have e2 : hexUnit (2 : ℤ) =
      Complex.exp (((5 * Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
    unfold hexUnit
    congr 1
    push_cast
    ring
  rw [e2, Complex.mul_im, Complex.exp_ofReal_mul_I_im,
    show (5 * Real.pi / 6 : ℝ) = Real.pi - Real.pi / 6 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_six]
  simp
  ring


end StatMech.Universality
