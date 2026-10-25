/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame


namespace StatMech.Universality

open scoped BigOperators


theorem hhw_critFacts_of_finsetBound {W : Type*} (f : W → ℝ)
    (hnn : ∀ w, 0 ≤ f w)
    (hbd : ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1) :
    Summable f ∧ (∑' w, f w) ≤ 1 :=
  ⟨summable_of_sum_le hnn hbd, Real.tsum_le_of_sum_le hnn hbd⟩


theorem hhw_finsetBound_of_boundary {W : Type*} (f : W → ℝ)
    (cl ct : ℝ) (hcl : 0 ≤ cl) (hct : 0 ≤ ct)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
    ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 := by
  intro s
  have h := hbdry s
  nlinarith [mul_nonneg hcl (hlam s), mul_nonneg hct (htau s)]


theorem hhw_critSummable_of_boundary {W : Type*} (f : W → ℝ)
    (cl ct : ℝ) (hcl : 0 ≤ cl) (hct : 0 ≤ ct)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hnn : ∀ w, 0 ≤ f w)
    (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
    Summable f :=
  summable_of_sum_le hnn
    (hhw_finsetBound_of_boundary f cl ct hcl hct lam tau hlam htau hbdry)


theorem hhw_critLeOne_of_boundary {W : Type*} (f : W → ℝ)
    (cl ct : ℝ) (hcl : 0 ≤ cl) (hct : 0 ≤ ct)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hnn : ∀ w, 0 ≤ f w)
    (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ s, f w) = 1) :
    (∑' w, f w) ≤ 1 :=
  Real.tsum_le_of_sum_le hnn
    (hhw_finsetBound_of_boundary f cl ct hcl hct lam tau hlam htau hbdry)


theorem hhw_finsetBound_of_singleStrip {W : Type*} (f : W → ℝ)
    (cl ct : ℝ) (hcl : 0 ≤ cl) (hct : 0 ≤ ct)
    (hnn : ∀ w, 0 ≤ f w)
    (strip : Finset W → Finset W)
    (hsub : ∀ s, s ⊆ strip s)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s : Finset W, cl * lam s + ct * tau s + (∑ w ∈ strip s, f w) = 1) :
    ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 := by
  intro s
  have hmono : ∑ w ∈ s, f w ≤ ∑ w ∈ strip s, f w :=
    Finset.sum_le_sum_of_subset_of_nonneg (hsub s) (fun w _ _ => hnn w)
  have h := hbdry s
  nlinarith [mul_nonneg hcl (hlam s), mul_nonneg hct (htau s), hmono]


end StatMech.Universality
