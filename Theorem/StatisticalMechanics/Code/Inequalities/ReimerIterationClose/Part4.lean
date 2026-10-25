/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part3
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rit_boxDownCompMono_eq_of_isLowerSet (w : α → Bool → ℝ) (i : α) {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      = wprob w (disjointOccurrence (familyEvent (Down.compression i 𝒜))
          (familyEvent (Down.compression i ℬ))) := by
  rw [downComp_eq_self_of_isLowerSet h𝒜, downComp_eq_self_of_isLowerSet hℬ]


theorem rit_boxDownCompMono_fin0 : rit_BoxDownCompMono (Fin 0) := by
  intro w _ _ i _ _; exact Fin.elim0 i


theorem rit_box_iterDownComp_mono (hmono : rit_BoxDownCompMono α) {w : α → Bool → ℝ}
    (hw0 : ∀ x b, 0 ≤ w x b) (hsym : ∀ x, w x false = w x true) (cs : List α)
    (𝒜 ℬ : Finset (Finset α)) :
    wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      ≤ wprob w (disjointOccurrence (familyEvent (iterDownComp cs 𝒜))
          (familyEvent (iterDownComp cs ℬ))) := by
  induction cs with
  | nil => simp
  | cons i cs ih =>
      rw [iterDownComp_cons, iterDownComp_cons]
      exact le_trans ih (hmono w hw0 hsym i (iterDownComp cs 𝒜) (iterDownComp cs ℬ))


theorem rit_reimer_wprob_symm_of_boxMono (hmono : rit_BoxDownCompMono α) (w : α → Bool → ℝ)
    (hw0 : ∀ x b, 0 ≤ w x b) (hw1 : ∀ x, w x false + w x true = 1)
    (hsym : ∀ x, w x false = w x true) (A B : Set (ConfigSpace α)) :
    wprob w (disjointOccurrence A B) ≤ wprob w A * wprob w B := by
  set 𝒜 := eventFamily A with h𝒜def
  set ℬ := eventFamily B with hℬdef
  have hA : A = familyEvent 𝒜 := (rit_familyEvent_eventFamily A).symm
  have hB : B = familyEvent ℬ := (rit_familyEvent_eventFamily B).symm
  obtain ⟨cs, hlA, hlB⟩ := rit_exists_common_iterDownComp_isLowerSet 𝒜 ℬ
  rw [hA, hB]
  calc wprob w (disjointOccurrence (familyEvent 𝒜) (familyEvent ℬ))
      ≤ wprob w (disjointOccurrence (familyEvent (iterDownComp cs 𝒜))
          (familyEvent (iterDownComp cs ℬ))) := rit_box_iterDownComp_mono hmono hw0 hsym cs 𝒜 ℬ
    _ ≤ fmarg w (iterDownComp cs 𝒜) * fmarg w (iterDownComp cs ℬ) :=
        reimer_fmarg_of_isLowerSet w hw0 hw1 hlA hlB
    _ = fmarg w 𝒜 * fmarg w ℬ := by
        rw [rit_fmarg_symm_iterDownComp hsym, rit_fmarg_symm_iterDownComp hsym]
    _ = wprob w (familyEvent 𝒜) * wprob w (familyEvent ℬ) := by
        rw [fmarg_eq_wprob_familyEvent, fmarg_eq_wprob_familyEvent]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rit_reimer_inequality_half_of_boxMono (hmono : rit_BoxDownCompMono α)
    (A B : Set (ConfigSpace α)) :
    (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real A
        * (bernoulliProductMeasure (E := α) (1/2) (by norm_num)).real B := by
  set φ : α → Bool → ℝ :=
    fun (_ : α) (b : Bool) => (bernoulliMeasure (1/2) (by norm_num)).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  have hf : (bernoulliMeasure (1/2 : ℝ≥0) (by norm_num)).real {false} = (1/2 : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal,
      NNReal.coe_sub (by norm_num), NNReal.coe_one]; norm_num
  have ht : (bernoulliMeasure (1/2 : ℝ≥0) (by norm_num)).real {true} = (1/2 : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]; norm_num
  have hφ1 : ∀ x, φ x false + φ x true = 1 := by
    intro x; simp only [hφ]; rw [hf, ht]; norm_num
  have hsym : ∀ x, φ x false = φ x true := by
    intro x; simp only [hφ]; rw [hf, ht]
  rw [bernoulli_real_eq_wprob (by norm_num) (disjointOccurrence A B),
    bernoulli_real_eq_wprob (by norm_num) A, bernoulli_real_eq_wprob (by norm_num) B]
  exact rit_reimer_wprob_symm_of_boxMono hmono φ hφ0 hφ1 hsym A B


end StatMech
