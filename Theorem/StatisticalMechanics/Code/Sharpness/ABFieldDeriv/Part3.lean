/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarskyUncond
import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
import Def.StatisticalMechanics.Code.Sharpness.ABFieldDeriv.Part3
open MeasureTheory Set Finset Function
open scoped NNReal ENNReal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech


variable {E : Type*} [Fintype E] [DecidableEq E]


lemma hasDerivAt_qField (h : ℝ) : HasDerivAt qField (Real.exp (-h)) h := by
  unfold qField
  have h1 : HasDerivAt (fun h : ℝ => Real.exp (-h)) (Real.exp (-h) * (-1)) h :=
    (Real.hasDerivAt_exp (-h)).comp h (by simpa using (hasDerivAt_id h).neg)
  have h2 : HasDerivAt (fun h : ℝ => 1 - Real.exp (-h)) (-(Real.exp (-h) * (-1))) h := by
    simpa using (hasDerivAt_const h (1 : ℝ)).sub h1
  convert h2 using 1; ring


lemma qField_mem (h : ℝ) (hh : 0 ≤ h) : 0 ≤ qField h ∧ qField h ≤ 1 := by
  unfold qField
  have hle1 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpos : 0 < Real.exp (-h) := Real.exp_pos _
  exact ⟨by linarith, by linarith⟩


theorem hasDerivAt_field_profile (s : Finset E) (p : E → ℝ) (A : Set (ConfigSpace E))
    (hA : IsIncreasing A) (h : ℝ) :
    HasDerivAt (fun h => probV (paramOn s (qField h) p) A)
      ((∑ e ∈ s, pivotalProbV (paramOn s (qField h) p) A e) * Real.exp (-h)) h := by
  have hcomp := (hasDerivAt_probV_paramOn s p A hA (qField h)).comp h (hasDerivAt_qField h)
  simpa [Function.comp] using hcomp


theorem deriv_field_profile (s : Finset E) (p : E → ℝ) (A : Set (ConfigSpace E))
    (hA : IsIncreasing A) (h : ℝ) :
    deriv (fun h => probV (paramOn s (qField h) p) A) h
      = ∑ e ∈ s, pivotalProbV (paramOn s (qField h) p) A e * Real.exp (-h) := by
  rw [(hasDerivAt_field_profile s p A hA h).deriv, Finset.sum_mul]


theorem abfd_field_influence_sum (s : Finset E) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (h : ℝ) (hh : 0 ≤ h) :
    let infl := fun e => pivotalProbV (paramOn s (qField h) p) A e * Real.exp (-h)
    (∑ e ∈ s, infl e = deriv (fun h => probV (paramOn s (qField h) p) A) h) ∧
      (∀ e ∈ s, 0 ≤ infl e) ∧
      (0 ≤ deriv (fun h => probV (paramOn s (qField h) p) A) h) := by
  intro infl
  
  have hqmem := qField_mem h hh
  have hparam : ∀ e, 0 ≤ paramOn s (qField h) p e ∧ paramOn s (qField h) p e ≤ 1 := by
    intro e; unfold paramOn; by_cases he : e ∈ s
    · rw [if_pos he]; exact hqmem
    · rw [if_neg he]; exact hp e
  have hinfl_nn : ∀ e ∈ s, 0 ≤ infl e := by
    intro e _
    exact mul_nonneg (pivotalProbV_nonneg _ hparam A e) (le_of_lt (Real.exp_pos _))
  refine ⟨?_, hinfl_nn, ?_⟩
  · rw [deriv_field_profile s p A hA h]
  · rw [deriv_field_profile s p A hA h]
    exact Finset.sum_nonneg hinfl_nn


end Sharpness


namespace Sharpness

open ConfigSpace StatMech

variable {E : Type} [Fintype E] [DecidableEq E]


theorem abfd_aizenmanBarsky_of_core (s : Finset E) (p : ℝ → E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (J : ℝ) (hJ0 : 0 ≤ J) (Jcoef : E → ℝ)
    (hJnn : ∀ e ∈ s, 0 ≤ Jcoef e) (hJle : ∀ e ∈ s, Jcoef e ≤ J)
    (hJsum : ∑ e ∈ s, Jcoef e = J)
    (piv : ℝ → ℝ → E → ℝ)
    (M : ℝ → ℝ → ℝ)
    (hM : M = fun β h => probV (paramOn s (qField h) (p β)) A)
    (hMnn : ∀ β h, 0 ≤ M β h)
    (hβrusso : ∀ β h, deriv (fun β => M β h) β = ∑ e ∈ s, piv β h e)
    (hbk : ∀ β h, ∀ e ∈ s, piv β h e ≤
      Jcoef e * M β h * (pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h)))
    (hfield_nn : ∀ β h,
      (∀ e ∈ s, 0 ≤ pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h))
      ∧ (0 ≤ deriv (fun h => M β h) h)) :
    AizenmanBarskyInequality M J := by
  apply aizenmanBarsky_of_geometricCore_and_inputs M J hJ0
  intro β h
  obtain ⟨hinfl_nn, hdMdh_nn⟩ := hfield_nn β h
  
  have hMfield : (fun h => M β h) = fun h => probV (paramOn s (qField h) (p β)) A := by
    funext h'; rw [hM]
  have hinfl_eq : ∑ e ∈ s, pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h)
      = deriv (fun h => M β h) h := by
    rw [hMfield, deriv_field_profile s (p β) A hA h]
  exact ⟨E, s, Jcoef,
    fun e => pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h),
    fun e => piv β h e, hMnn β h, hJnn, hinfl_nn, hβrusso β h, hbk β h, hJsum,
    hinfl_eq, hJle, hdMdh_nn⟩


theorem abfd_hfield_nn_eq_M2 (s : Finset E) (p : ℝ → E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (hp : ∀ β e, 0 ≤ p β e ∧ p β e ≤ 1)
    (β h : ℝ) (hh : 0 ≤ h) :
    (∀ e ∈ s, 0 ≤ pivotalProbV (paramOn s (qField h) (p β)) A e * Real.exp (-h))
    ∧ (0 ≤ deriv (fun h => probV (paramOn s (qField h) (p β)) A) h) := by
  have hM2 := abfd_field_influence_sum s (p β) (hp β) A hA h hh
  simp only at hM2
  exact ⟨hM2.2.1, hM2.2.2⟩

end Sharpness
end StatMech
