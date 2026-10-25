/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc2_whynotperedge
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.CovLowerBound

open StatMech.OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc3_weight_eq_of_match {μ : ConfigSpace E → ℝ} {ν : E → Bool → ℝ}
    (hmatch : ∀ g, expect ν g = Lindeberg.mean μ g) (ω₀ : ConfigSpace E) :
    weight ν ω₀ = μ ω₀ := by
  have h := hmatch (fun ω => if ω = ω₀ then (1 : ℝ) else 0)
  have hL : expect ν (fun ω => if ω = ω₀ then (1 : ℝ) else 0) = weight ν ω₀ := by
    unfold OSSS.expect
    rw [Finset.sum_eq_single ω₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : Lindeberg.mean μ (fun ω => if ω = ω₀ then (1 : ℝ) else 0) = μ ω₀ := by
    unfold Lindeberg.mean
    rw [Finset.sum_eq_single ω₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at h; exact h


theorem oc3_cov_eq_of_match {μ : ConfigSpace E → ℝ} {ν : E → Bool → ℝ}
    (hmatch : ∀ g, expect ν g = Lindeberg.mean μ g) (F G : ConfigSpace E → ℝ) :
    cov ν F G = Lindeberg.cov μ F G := by
  unfold cov Lindeberg.cov
  rw [hmatch (fun ω => F ω * G ω), hmatch F, hmatch G]


theorem oc3_coordI_flipAt_ne (e e' : E) (he : e ≠ e') (ω : ConfigSpace E) :
    coordI e' (flipAt e ω) = coordI e' ω := by
  unfold coordI
  rw [flipAt_eval_ne e e' (Ne.symm he) ω]


theorem oc3_cov_coordI_cross {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (e e' : E) (he : e ≠ e') :
    cov ν (coordI e) (coordI e') = 0 :=
  cov_coordI_indep hν e (coordI e') (fun ω => oc3_coordI_flipAt_ne e e' he ω)


end Walls
end StatMech
