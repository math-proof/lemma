/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Class.v1.Atlas.GeometryOfManifolds.code.DifferentialForms
public section

set_option autoImplicit false


/-- Poincaré homotopy operator on Euclidean space: there exist linear maps $K_p : \Omega^{p+1} \to \Omega^p$ satisfying $dK + Kd = \mathrm{id}$ and $K\,0 = 0$. -/
structure DFSMorphism (Ω₁ : ℕ → Type*) (VF₁ : Type*)
    (Ω₂ : ℕ → Type*) (VF₂ : Type*)
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂] where
  pullback : ∀ {p : ℕ}, Ω₂ p → Ω₁ p
  pullback_add : ∀ {p : ℕ} (α β : Ω₂ p),
    pullback (α + β) = pullback α + pullback β
  pullback_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω₂ p),
    pullback (r • α) = r • pullback α
  pullback_comm_d : ∀ {p : ℕ} (α : Ω₂ p),
    pullback (inst₂.d α) = inst₁.d (pullback α)

