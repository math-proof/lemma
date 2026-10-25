/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Class.v1.Atlas.GeometryOfManifolds.code.DifferentialForms
set_option autoImplicit false

attribute [reducible, instance] DifferentialFormSpace.instAddCommGroup
attribute [reducible, instance] DifferentialFormSpace.instModule

attribute [instance] HasComplexScalars.instComplexModule
attribute [instance] HasComplexScalars.instScalarTower
attribute [instance] HasComplexScalars.instSMulCommClass


namespace DifferentialFormSpace

variable {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]

/-- Multiplication of a function by the zero $p$-form yields zero: $f \cdot 0 = 0$. -/
lemma fMul_zero {p : ℕ} (f : Ω 0) : inst.fMul f (0 : Ω p) = 0 := by
  have h : inst.fMul f (0 : Ω p) + inst.fMul f (0 : Ω p) =
           inst.fMul f (0 : Ω p) := by
    rw [← inst.fMul_add_right, add_zero]
  have h2 := congr_arg (· - inst.fMul f (0 : Ω p)) h
  simp [add_sub_cancel_right] at h2; exact h2

/-- Interior product with the zero form is zero: $\iota_X 0 = 0$. -/
lemma ι_zero_val (X : VF) {p : ℕ} :
    inst.ι X (0 : Ω (p + 1)) = (0 : Ω p) := by
  have h := inst.ι_smul X (0 : ℝ) (0 : Ω (p + 1))
  simp [zero_smul] at h; exact h

/-- The exterior derivative commutes with negation: $d(-\alpha) = -d\alpha$. -/
lemma d_neg {p : ℕ} (α : Ω p) : inst.d (-α) = -(inst.d α) := by
  have h := inst.d_smul (-1 : ℝ) α; simp at h; exact h

/-- Inductive step in the proof of Cartan's magic formula: from the relation $d(\mathcal{L}_X \gamma) = d(\iota_X d\gamma)$ at degree $p$, deduce $\mathcal{L}_X \beta = d(\iota_X \beta) + \iota_X(d\beta)$ at degree $p+1$. -/
theorem cartan_step (X : VF) {p : ℕ}
    (ih : ∀ (γ : Ω p), inst.d (inst.L X γ) = inst.d (inst.ι X (inst.d γ)))
    (β : Ω (p + 1)) :
    inst.L X β = inst.d (inst.ι X β) + inst.ι X (inst.d β) := by

  have key : inst.L X β - inst.d (inst.ι X β) - inst.ι X (inst.d β) = 0 := by
    apply inst.ext_fdα
      (fun β => inst.L X β - inst.d (inst.ι X β) - inst.ι X (inst.d β))
    ·
      intro a b
      simp only [inst.L_add, inst.ι_add, inst.d_add]
      abel
    ·
      intro r a
      simp only [inst.L_smul, inst.ι_smul, inst.d_smul]
      rw [smul_sub, smul_sub]
    ·
      intro f α

      have lhs_eq : inst.L X (inst.fMul f (inst.d α)) =
        inst.fMul (inst.ι X (inst.d f)) (inst.d α) +
        inst.fMul f (inst.d (inst.ι X (inst.d α))) := by
        rw [inst.L_fMul, inst.L_comm_d, inst.L_zero_eq_ι_d, ih]

      have d_fdα : inst.d (inst.fMul f (inst.d α)) =
        inst.wedge1 (inst.d f) (inst.d α) := by
        rw [inst.d_fMul, inst.d_squared, fMul_zero, add_zero]

      have rhs_eq : inst.d (inst.ι X (inst.fMul f (inst.d α))) +
        inst.ι X (inst.d (inst.fMul f (inst.d α))) =
        inst.fMul (inst.ι X (inst.d f)) (inst.d α) +
        inst.fMul f (inst.d (inst.ι X (inst.d α))) := by
        rw [inst.ι_fMul, inst.d_fMul, d_fdα, inst.ι_wedge1]
        abel
      rw [lhs_eq, ← rhs_eq]; abel

  have heq : inst.L X β = inst.L X β - inst.d (inst.ι X β) -
    inst.ι X (inst.d β) + (inst.d (inst.ι X β) + inst.ι X (inst.d β)) := by abel
  rw [key, zero_add] at heq; exact heq

/-- Cartan's magic formula: $\mathcal{L}_X \alpha = d(\iota_X \alpha) + \iota_X(d\alpha)$ on any differential form. -/
theorem cartan_formula (X : VF) {p : ℕ} (α : Ω (p + 1)) :
    inst.L X α = inst.d (inst.ι X α) + inst.ι X (inst.d α) := by
  induction p with
  | zero =>

    exact cartan_step X (fun γ => by rw [inst.L_zero_eq_ι_d]) α
  | succ n ih_ind =>

    exact cartan_step X (fun γ => by
      rw [ih_ind γ, inst.d_add, inst.d_squared, zero_add]) α

end DifferentialFormSpace
