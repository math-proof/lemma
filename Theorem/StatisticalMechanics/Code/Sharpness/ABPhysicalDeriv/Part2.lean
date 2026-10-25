/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABPhysicalDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostInfluence
import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
import Def.StatisticalMechanics.Code.Sharpness.ABPhysicalDeriv
open Finset Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem abpd_hasDerivAt_beta_field_profile (s : Finset E) (q : ℝ) (J : E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (beta : ℝ) :
    HasDerivAt (fun b => probV (abpdBetaFieldParams s q J b) A)
      (∑ e, (if e ∈ s then 0 else J e * Real.exp (-beta * J e)) *
        pivotalProbV (abpdBetaFieldParams s q J beta) A e) beta := by
  refine abpd_hasDerivAt_probV_profile _ _ beta ?_ A hA
  intro e
  unfold abpdBetaFieldParams paramOn
  by_cases he : e ∈ s
  · simp only [he, if_true]
    exact hasDerivAt_const beta q
  · simp only [he, if_false]
    exact shr_pBeta_hasDerivAt (J e) beta


theorem abpd_deriv_beta_field_profile (s : Finset E) (q : ℝ) (J : E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (beta : ℝ) :
    deriv (fun b => probV (abpdBetaFieldParams s q J b) A) beta =
      ∑ e, (if e ∈ s then 0 else J e * Real.exp (-beta * J e)) *
        pivotalProbV (abpdBetaFieldParams s q J beta) A e :=
  (abpd_hasDerivAt_beta_field_profile s q J A hA beta).deriv


theorem abpd_deriv_beta_field_profile_closed (s : Finset E) (q : ℝ) (J : E → ℝ)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (beta : ℝ) :
    deriv (fun b => probV (abpdBetaFieldParams s q J b) A) beta =
      ∑ e, if e ∈ s then 0 else
        J e * probV (abpdBetaFieldParams s q J beta) (abgiClosedPivotal e A) := by
  rw [abpd_deriv_beta_field_profile s q J A hA beta]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ s
  · simp [he]
  · simp only [he, if_false]
    rw [abgi_probV_closedPivotal]
    have hclosed : 1 - abpdBetaFieldParams s q J beta e =
        Real.exp (-beta * J e) := by
      simp [abpdBetaFieldParams, paramOn, he, pBeta]
    rw [hclosed]
    ring

end Sharpness
end StatMech
