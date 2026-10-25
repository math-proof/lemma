/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Def.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part3


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

@[simp] theorem hexAWLowerSlantWitness_heading (L : ℕ) :
    hexAWHeading (hexAWLowerSlantWitness L).vtx.1
      (hexAWLowerSlantWitness L).edge = 0 := rfl

@[simp] theorem hexAWUpperSlantWitness_heading (L : ℕ) :
    hexAWHeading (hexAWUpperSlantWitness L).vtx.1
      (hexAWUpperSlantWitness L).edge = 2 := rfl

theorem hexAWLowerSlantWitness_mem_boundary (L : ℕ) :
    hexAWLowerSlantWitness L ∈ hexAWBoundaryIncidences 2 L := by
  rw [hexAW_mem_boundary_iff]
  unfold hexAWIsInterior hexAWLowerSlantWitness
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWNeighbor, hexAWLowerSlantWitnessCoord, hexAWInStrip,
    hexAWBookRe2, hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
    hexAWTrans]
  omega

theorem hexAWUpperSlantWitness_mem_boundary (L : ℕ) :
    hexAWUpperSlantWitness L ∈ hexAWBoundaryIncidences 2 L := by
  rw [hexAW_mem_boundary_iff]
  unfold hexAWIsInterior hexAWUpperSlantWitness
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWNeighbor, hexAWUpperSlantWitnessCoord, hexAWInStrip,
    hexAWBookRe2, hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
    hexAWTrans]
  omega


theorem hexAWLowerSlant_turning_ne_source
    (L : ℕ) (ts : List ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid (hexAWLowerSlantWitness L).vtx.1
        (hexAWLowerSlantWitness L).edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor (hexAWLowerSlantWitness L).vtx.1
        (hexAWLowerSlantWitness L).edge)) :
    (ofTurns hexAWStart 1 ts).turning ≠ -(2 * Real.pi / 3) := by
  intro hturn
  have hdvd := hexAWEndpoint_finalHeading_mod
    (hexAWLowerSlantWitness L) ts hend hexit
  simp only [hexAWLowerSlantWitness_heading, sub_zero] at hdvd
  have hformula := hexInfra_turning_eq_headAccum_sub hexAWStart 1 ts
  have hhead : hexInfra_headAccum 1 ts = -1 := by
    rw [hturn] at hformula
    norm_num at hformula
    have hp := Real.pi_pos
    have hmul : Real.pi *
        ((hexInfra_headAccum 1 ts : ℝ) + 1) = 0 := by
      calc
        Real.pi * ((hexInfra_headAccum 1 ts : ℝ) + 1) =
            3 * ((Real.pi / 3) *
              ((hexInfra_headAccum 1 ts : ℝ) - 1) -
                (-(2 * Real.pi / 3))) := by ring
        _ = 0 := by rw [← hformula]; ring
    have hreal : (hexInfra_headAccum 1 ts : ℝ) + 1 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
    have hcast : (hexInfra_headAccum 1 ts : ℝ) = (-1 : ℝ) := by
      linarith
    exact_mod_cast hcast
  rw [hhead] at hdvd
  omega


theorem hexAWUpperSlant_turning_ne_source
    (L : ℕ) (ts : List ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid (hexAWUpperSlantWitness L).vtx.1
        (hexAWUpperSlantWitness L).edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor (hexAWUpperSlantWitness L).vtx.1
        (hexAWUpperSlantWitness L).edge)) :
    (ofTurns hexAWStart 1 ts).turning ≠ 2 * Real.pi / 3 := by
  intro hturn
  have hdvd := hexAWEndpoint_finalHeading_mod
    (hexAWUpperSlantWitness L) ts hend hexit
  simp only [hexAWUpperSlantWitness_heading] at hdvd
  have hformula := hexInfra_turning_eq_headAccum_sub hexAWStart 1 ts
  have hhead : hexInfra_headAccum 1 ts = 3 := by
    rw [hturn] at hformula
    norm_num at hformula
    have hp := Real.pi_pos
    have hmul : Real.pi *
        ((hexInfra_headAccum 1 ts : ℝ) - 3) = 0 := by
      calc
        Real.pi * ((hexInfra_headAccum 1 ts : ℝ) - 3) =
            3 * ((Real.pi / 3) *
              ((hexInfra_headAccum 1 ts : ℝ) - 1) -
                (2 * Real.pi / 3)) := by ring
        _ = 0 := by rw [← hformula]; ring
    have hreal : (hexInfra_headAccum 1 ts : ℝ) - 3 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hp)
    have hcast : (hexInfra_headAccum 1 ts : ℝ) = (3 : ℝ) := by
      linarith
    exact_mod_cast hcast
  rw [hhead] at hdvd
  omega

end
end StatMech.Universality
