/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/DihedralHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelation
import Lemma.Real.EqSigma.of.EqBilinForm_E_0
open Finset BigOperators Real


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The composition $\sigma_s \sigma_t$ is additive. -/
theorem sigma_comp_add (M : CoxeterMatrix B) (s t : B) (v₁ v₂ : B → ℝ) :
    sigma M s (sigma M t (v₁ + v₂)) =
    sigma M s (sigma M t v₁) + sigma M s (sigma M t v₂) := by
  rw [sigma_add M t, sigma_add M s]

/-- The composition $\sigma_s \sigma_t$ commutes with scalar multiplication. -/
theorem sigma_comp_smul (M : CoxeterMatrix B) (s t : B) (c : ℝ) (v : B → ℝ) :
    sigma M s (sigma M t (c • v)) = c • sigma M s (sigma M t v) := by
  rw [sigma_smul M t, sigma_smul M s]

/-- The $n$-fold iterate of $\sigma_s \sigma_t$ is additive. -/
theorem iterate_sigma_comp_add (M : CoxeterMatrix B) (s t : B) (n : ℕ) (v₁ v₂ : B → ℝ) :
    (fun w => sigma M s (sigma M t w))^[n] (v₁ + v₂) =
    (fun w => sigma M s (sigma M t w))^[n] v₁ +
    (fun w => sigma M s (sigma M t w))^[n] v₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_comp_add]

/-- The $n$-fold iterate of $\sigma_s \sigma_t$ commutes with scalar
multiplication. -/
theorem iterate_sigma_comp_smul (M : CoxeterMatrix B) (s t : B) (n : ℕ) (c : ℝ) (v : B → ℝ) :
    (fun w => sigma M s (sigma M t w))^[n] (c • v) =
    c • (fun w => sigma M s (sigma M t w))^[n] v := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_comp_smul]


/-- The $n$-fold iterate of $\sigma_s \sigma_t$ fixes any vector orthogonal to
both $e_s$ and $e_t$. -/
theorem iterate_sigma_comp_fixes_orthogonal (M : CoxeterMatrix B) (s t : B) (n : ℕ)
    (w : B → ℝ) (hs : bilinForm M w (e s) = 0) (ht : bilinForm M w (e t) = 0) :
    (fun v => sigma M s (sigma M t v))^[n] w = w := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih, sigma_comp_fixes_orthogonal M s t w hs ht]

end CoxeterGroup
