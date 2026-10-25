/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem hexEndpointCoordRun_base_compatible :
    (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base []).ColorCompatible := by
  left
  exact ⟨Or.inl rfl, dvd_zero 3⟩


theorem hexEndpointCoordRun_step_compatible
    (p d : HexReturnCoord) (t : ℤ)
    (hc : (HexEndpointCoordRun.mk p d).ColorCompatible)
    (ht : t = 1 ∨ t = -1) :
    (HexEndpointCoordRun.mk (p.add (d.turn t)) (d.turn t)).ColorCompatible := by
  rcases hc with ⟨hd, hp⟩ | ⟨hd, hp⟩ <;>
    rcases hd with rfl | rfl | rfl <;>
    rcases ht with rfl | rfl
  all_goals
    simp only [HexEndpointCoordRun.ColorCompatible,
      HexReturnCoord.IsEvenDir, HexReturnCoord.IsOddDir,
      HexReturnCoord.turn, HexReturnCoord.left, HexReturnCoord.right,
      HexReturnCoord.add]
    norm_num at hp ⊢
  all_goals omega


theorem hexEndpointCoordRun_compatible (p d : HexReturnCoord) (ts : List ℤ)
    (hc : (HexEndpointCoordRun.mk p d).ColorCompatible)
    (hunit : d.IsUnit)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hexEndpointCoordRun p d ts).ColorCompatible := by
  induction ts generalizing p d with
  | nil => exact hc
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : e.IsUnit := HexReturnCoord.isUnit_turn hunit ht
      exact ih (p.add e) e
        (hexEndpointCoordRun_step_compatible p d t hc ht) he htail


theorem hexEndpointCoordRun_geometry (p d : HexReturnCoord) (m s : ℂ)
    (h : ℤ) (ts : List ℤ)
    (hdir : halfStep h = d.value * s)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    let r := hexEndpointCoordRun p d ts
    hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) =
        m + halfStep h + 2 * ((r.pos.value - p.value) * s) ∧
      halfStep (hexInfra_headAccum h ts) = r.dir.value * s := by
  induction ts generalizing p d m h with
  | nil =>
      constructor
      · simp [hexEndpointCoordRun]
      · simpa [hexEndpointCoordRun] using hdir
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : halfStep (h + t) = e.value * s :=
        hexReturn_halfStep_turn s h d t hdir ht
      have hrec := ih (p.add e) e
        (m + halfStep h + halfStep (h + t)) (h + t) he htail
      simp only [hexEndpointCoordRun, hexInfra_midAccum_cons,
        hexInfra_headAccum_cons]
      simp only [HexReturnCoord.value_add] at hrec
      constructor
      · rw [hrec.1, he]
        ring
      · exact hrec.2


theorem hexEndpoint_return_even_direction (m : ℂ) (h : ℤ) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hreturn : hexInfra_midAccum m h ts +
        halfStep (hexInfra_headAccum h ts) = m + halfStep h) :
    (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).dir.IsEvenDir := by
  have hbase : halfStep h = HexReturnCoord.base.value * halfStep h := by simp
  have hgeom := hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base m (halfStep h) h ts hbase hlegal
  have hmul : (2 : ℂ) *
      ((hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos.value *
        halfStep h) = 0 := by
    have := hgeom.1
    rw [hreturn] at this
    simp only [HexReturnCoord.value_zero, sub_zero] at this
    linear_combination -this
  have hposValue :
      (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos.value = 0 := by
    rcases mul_eq_zero.mp hmul with htwo | hrest
    · norm_num at htwo
    · rcases mul_eq_zero.mp hrest with hvalue | hstep
      · exact hvalue
      · exact absurd hstep (hexConcrete_halfStep_ne h)
  have hpos :
      (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos =
        HexReturnCoord.zero :=
    hexReturnCoord_value_eq_zero hposValue
  have hc := hexEndpointCoordRun_compatible HexReturnCoord.zero
    HexReturnCoord.base ts hexEndpointCoordRun_base_compatible
      HexReturnCoord.base_isUnit hlegal
  rcases hc with heven | hodd
  · exact heven.1
  · rw [hpos] at hodd
    rcases hodd.2 with ⟨k, hk⟩
    norm_num [HexReturnCoord.zero] at hk
    exfalso
    omega

theorem hexEndpoint_halfStep_add_two (h : ℤ) :
    halfStep (h + 2) = hexOmega * halfStep h := by
  unfold halfStep
  rw [hexUnit_add_two]
  ring

theorem hexEndpoint_halfStep_add_four (h : ℤ) :
    halfStep (h + 4) = hexOmega ^ 2 * halfStep h := by
  unfold halfStep
  rw [hexUnit_add_four]
  ring

@[simp] theorem hexEndpoint_halfStep_add_six (h : ℤ) :
    halfStep (h + 6) = halfStep h := by
  unfold halfStep
  rw [show (h + 6 : ℤ) = (h + 3) + 3 by ring,
    hexUnit_add_three, hexUnit_add_three]
  ring

theorem hexEndpoint_halfStep_add_three (h : ℤ) :
    halfStep (h + 3) = -halfStep h := by
  unfold halfStep
  rw [hexUnit_add_three]
  ring

theorem hexEndpoint_halfStep_sub_one (h : ℤ) :
    halfStep (h - 1) = -(hexOmega * halfStep h) := by
  have key := hexUnit_add_three (h - 1)
  rw [show (h - 1 + 3 : ℤ) = h + 2 by ring, hexUnit_add_two] at key
  unfold halfStep
  linear_combination (1 / 2 : ℂ) * key

theorem hexEndpoint_halfStep_add_one (h : ℤ) :
    halfStep (h + 1) = -(hexOmega ^ 2 * halfStep h) := by
  have key := hexUnit_add_three (h + 1)
  rw [show (h + 1 + 3 : ℤ) = h + 4 by ring, hexUnit_add_four] at key
  unfold halfStep
  linear_combination (1 / 2 : ℂ) * key


theorem hexAW_halfStep_edge_one (c : HexAWCoord) :
    halfStep (hexAWHeading c 1) =
      hexOmega * halfStep (hexAWHeading c 0) := by
  rcases c with ⟨i, j, color⟩
  cases color
  · have h := hexEndpoint_halfStep_add_two 4
    rw [show (4 + 2 : ℤ) = 0 + 6 by norm_num,
      hexEndpoint_halfStep_add_six] at h
    simpa [hexAWHeading] using h
  · have h := hexEndpoint_halfStep_add_two 7
    rw [show (7 + 2 : ℤ) = 3 + 6 by norm_num,
      hexEndpoint_halfStep_add_six] at h
    simpa [hexAWHeading] using h


theorem hexAW_halfStep_edge_two (c : HexAWCoord) :
    halfStep (hexAWHeading c 2) =
      hexOmega ^ 2 * halfStep (hexAWHeading c 0) := by
  rcases c with ⟨i, j, color⟩
  cases color
  · have h := hexEndpoint_halfStep_add_four 4
    rw [show (4 + 4 : ℤ) = 2 + 6 by norm_num,
      hexEndpoint_halfStep_add_six] at h
    simpa [hexAWHeading] using h
  · have h := hexEndpoint_halfStep_add_four 7
    rw [show (7 + 4 : ℤ) = 5 + 6 by norm_num,
      hexEndpoint_halfStep_add_six] at h
    simpa [hexAWHeading] using h

theorem hexAWMid_sub_pos_eq_halfStep (c : HexAWCoord) (e : Fin 3) :
    hexAWMid c e - hexAWPos c = halfStep (hexAWHeading c e) := by
  simpa [halfStep] using hexAWMid_sub_pos c e


theorem hexAW_labelMid_eq_mid (c : HexAWCoord) (e : Fin 3) :
    labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e =
      hexAWMid c e := by
  fin_cases e
  · simp [labelMid]
  · simp only [labelMid]
    rw [hexAWMid_sub_pos_eq_halfStep,
      ← hexAW_halfStep_edge_one c,
      ← hexAWMid_sub_pos_eq_halfStep]
    ring_nf
    congr
  · simp only [labelMid]
    rw [hexAWMid_sub_pos_eq_halfStep,
      ← hexAW_halfStep_edge_two c,
      ← hexAWMid_sub_pos_eq_halfStep]
    ring_nf
    congr

theorem hexAW_base_du_ne_zero (c : HexAWCoord) :
    hexAWMid c 0 - hexAWPos c ≠ 0 := by
  rw [hexAWMid_sub_pos_eq_halfStep]
  exact hexConcrete_halfStep_ne _


end
end StatMech.Universality
