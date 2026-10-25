/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction
open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierC StatMech.Sharpness StatMech.Sharpness.FieldGhostDict


theorem leeYangBoxSpinProduct_ofReal
    (d n : ℕ) (beta h : ℝ) (A : Finset (Site d)) :
    leeYangBoxSpinProduct d beta A n (h : ℂ) =
      (isingExpectation (boxGraph d n) beta h
        (spinProd (boxSpinSupport d n A)) : ℂ) := by
  exact leeYangComplexFieldExpectation_ofReal _ beta h _

theorem leeYangBoxSpinProduct_analyticOnNhd_rightHalfPlane
    (d n : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta) (A : Finset (Site d)) :
    AnalyticOnNhd ℂ (leeYangBoxSpinProduct d beta A n)
      {h : ℂ | 0 < h.re} :=
  leeYangComplexFieldExpectation_analyticOnNhd_rightHalfPlane
    (boxGraph d n) hbeta _

theorem leeYangBoxSpinProduct_analyticOnNhd_leftHalfPlane
    (d n : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta) (A : Finset (Site d)) :
    AnalyticOnNhd ℂ (leeYangBoxSpinProduct d beta A n)
      {h : ℂ | h.re < 0} :=
  leeYangComplexFieldExpectation_analyticOnNhd_leftHalfPlane
    (boxGraph d n) hbeta _


theorem leeYangBoxSpinProduct_tendsto_of_nonneg_real_field
    (d : ℕ) (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (A : Finset (Site d)) :
    Tendsto (fun n => leeYangBoxSpinProduct d beta A n (h : ℂ)) atTop
      (nhds (Complex.ofReal (∫ omega, spinProd A omega
        ∂(freeState d beta h : Measure (ConfigSpace (Site d)))))) := by
  have hr := integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field
    d beta h hbeta hh A
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  refine hc.congr' ?_
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  filter_upwards [eventually_ge_atTop N] with n hn
  change Complex.ofReal (∫ omega, spinProd A omega
      ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d)))) = _
  rw [leeYangBoxSpinProduct_ofReal]
  exact congrArg Complex.ofReal (integral_freeMeasure_spinProd d n beta h A
    (hAN.trans (box_mono d hn)))


theorem isingExpectation_spinProd_neg_field
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (A : Finset V) :
    isingExpectation G beta (-h) (spinProd A) =
      (-1 : ℝ) ^ A.card * isingExpectation G beta h (spinProd A) := by
  unfold isingExpectation
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold isingProb
  rw [spinProd_flipV, isingWeight_flip, fgd_isingZ_neg]
  ring

theorem boxSpinSupport_card_eq
    (d n : ℕ) (A : Finset (Site d)) (hA : ↑A ⊆ box d n) :
    (boxSpinSupport d n A).card = A.card := by
  have hsupp : (boxSpinSupport d n A).image Subtype.val = A := by
    ext x
    constructor
    · rintro hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa [boxSpinSupport] using hy
    · intro hx
      rw [Finset.mem_image]
      exact ⟨⟨x, hA hx⟩, by simp [boxSpinSupport, hx], rfl⟩
  calc
    (boxSpinSupport d n A).card =
        ((boxSpinSupport d n A).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := congrArg Finset.card hsupp


theorem leeYangBoxSpinProduct_tendsto_of_neg_real_field
    (d : ℕ) (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : h < 0)
    (A : Finset (Site d)) :
    Tendsto (fun n => leeYangBoxSpinProduct d beta A n (h : ℂ)) atTop
      (nhds ((((-1 : ℝ) : ℂ) ^ A.card) *
        Complex.ofReal (∫ omega, spinProd A omega
          ∂(freeState d beta (-h) : Measure (ConfigSpace (Site d)))))) := by
  have hp := leeYangBoxSpinProduct_tendsto_of_nonneg_real_field
    d beta (-h) hbeta (neg_nonneg.mpr hh.le) A
  have hmul := (tendsto_const_nhds (x := ((-1 : ℝ) ^ A.card : ℂ))).mul hp
  refine hmul.congr' ?_
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [leeYangBoxSpinProduct_ofReal, leeYangBoxSpinProduct_ofReal]
  have hcard := boxSpinSupport_card_eq d n A
    (hAN.trans (box_mono d hn))
  have hs := isingExpectation_spinProd_neg_field (boxGraph d n) beta (-h)
    (boxSpinSupport d n A)
  rw [neg_neg, hcard] at hs
  exact_mod_cast hs.symm


end StatMech.FrontierA
