/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part2
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part3
open Finset


namespace StatMech.Sharpness

theorem shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) :
    shbParitySeriesMassOn S P x =
      Real.cosh x ^ S.card * shbParityPolynomialOn S P (Real.tanh x) := by
  unfold shbParitySeriesMassOn shbParityPolynomialOn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hP : P A
  · rw [if_pos hP, if_pos hP]
    simp_rw [shb_evenCurrentSeries_eq_cosh, shb_oddCurrentSeries_eq_sinh,
      shb_sinh_eq_cosh_mul_tanh]
    rw [Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.prod_const]
    have hsub : A ⊆ S := Finset.mem_powerset.mp hA
    rw [Finset.inter_eq_right.mpr hsub]
    have hcard := Finset.card_filter_add_card_filter_not
      (s := S) (fun e ↦ e ∈ A)
    simp only [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub] at hcard
    rw [mul_pow]
    calc
      Real.cosh x ^ A.card * Real.tanh x ^ A.card *
            Real.cosh x ^ ((S.filter fun e ↦ ¬ e ∈ A).card) =
          (Real.cosh x ^ A.card *
              Real.cosh x ^ ((S.filter fun e ↦ ¬ e ∈ A).card)) *
            Real.tanh x ^ A.card := by ring
      _ = Real.cosh x ^
              (A.card + (S.filter fun e ↦ ¬ e ∈ A).card) *
            Real.tanh x ^ A.card := by rw [pow_add]
      _ = Real.cosh x ^ S.card * Real.tanh x ^ A.card := by rw [hcard]
  · rw [if_neg hP, if_neg hP, mul_zero]


end StatMech.Sharpness
