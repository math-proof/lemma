/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.GeometryOfManifolds.code.DifferentialForms
set_option autoImplicit false

attribute [reducible, instance] DifferentialFormSpace.instAddCommGroup
attribute [reducible, instance] DifferentialFormSpace.instModule

attribute [instance] HasComplexScalars.instComplexModule
attribute [instance] HasComplexScalars.instScalarTower
attribute [instance] HasComplexScalars.instSMulCommClass


namespace DifferentialFormSpace

variable {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]

/-- A differential form $\alpha$ is closed when $d\alpha = 0$. -/
def IsClosed' (VF : Type*) [inst : DifferentialFormSpace Ω VF] {p : ℕ} (α : Ω p) : Prop :=
  inst.d α = 0

/-- A differential $(p+1)$-form $\alpha$ is exact when $\alpha = d\beta$ for some $p$-form $\beta$. -/
def IsExact' (VF : Type*) [inst : DifferentialFormSpace Ω VF] {p : ℕ} (α : Ω (p + 1)) : Prop :=
  ∃ (β : Ω p), α = inst.d β

/-- The setoid on closed $(p+1)$-forms whose quotient yields the de Rham cohomology $H^{p+1}_{dR}$: $\alpha \sim \beta$ iff $\alpha - \beta$ is exact. -/
def deRhamSetoid (p : ℕ) :
    Setoid {α : Ω (p + 1) // IsClosed' VF (inst := inst) α} where
  r α β := IsExact' VF (inst := inst) (α.val - β.val)
  iseqv := {
    refl := fun _ => ⟨0, by rw [sub_self]; exact d_zero_val.symm⟩
    symm := by
      intro a b ⟨γ, hγ⟩
      exact ⟨-γ, by rw [d_neg, ← hγ, neg_sub]⟩
    trans := by
      intro a b c ⟨δ₁, h₁⟩ ⟨δ₂, h₂⟩
      exact ⟨δ₁ + δ₂, by
        have : (↑a : Ω (p + 1)) - (↑c : Ω (p + 1)) =
          ((↑a : Ω (p + 1)) - (↑b : Ω (p + 1))) +
          ((↑b : Ω (p + 1)) - (↑c : Ω (p + 1))) := by abel
        rw [this, h₁, h₂, inst.d_add]⟩
  }

end DifferentialFormSpace
