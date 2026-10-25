/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
set_option autoImplicit false


/-- Axiomatic structure of a graded space $\Omega^\bullet$ of differential forms together with a space $VF$ of vector fields: includes wedge with functions and $1$-forms, exterior derivative $d$, interior product $\iota$, Lie derivative $\mathcal{L}$ and the algebraic relations they satisfy. -/
class DifferentialFormSpace (Ω : ℕ → Type*) (VF : Type*) where
  [instAddCommGroup : ∀ p, AddCommGroup (Ω p)]
  [instModule : ∀ p, Module ℝ (Ω p)]
  fMul : ∀ {p : ℕ}, Ω 0 → Ω p → Ω p
  wedge1 : ∀ {p : ℕ}, Ω 1 → Ω p → Ω (p + 1)
  d : ∀ {p : ℕ}, Ω p → Ω (p + 1)
  ι : VF → ∀ {p : ℕ}, Ω (p + 1) → Ω p
  L : VF → ∀ {p : ℕ}, Ω p → Ω p
  d_add : ∀ {p : ℕ} (α β : Ω p), d (α + β) = d α + d β
  d_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), d (r • α) = r • d α
  d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0
  d_fMul : ∀ {p : ℕ} (f : Ω 0) (α : Ω p),
    d (fMul f α) = wedge1 (d f) α + fMul f (d α)
  fMul_add_left : ∀ {p : ℕ} (f g : Ω 0) (α : Ω p),
    fMul (f + g) α = fMul f α + fMul g α
  fMul_add_right : ∀ {p : ℕ} (f : Ω 0) (α β : Ω p),
    fMul f (α + β) = fMul f α + fMul f β
  fMul_smul : ∀ {p : ℕ} (r : ℝ) (f : Ω 0) (α : Ω p),
    fMul (r • f) α = r • fMul f α
  wedge1_add_right : ∀ {p : ℕ} (ω : Ω 1) (α β : Ω p),
    wedge1 ω (α + β) = wedge1 ω α + wedge1 ω β
  wedge1_smul_right : ∀ {p : ℕ} (ω : Ω 1) (r : ℝ) (α : Ω p),
    wedge1 ω (r • α) = r • wedge1 ω α
  ι_add : ∀ (X : VF) {p : ℕ} (α β : Ω (p + 1)),
    ι X (α + β) = ι X α + ι X β
  ι_smul : ∀ (X : VF) {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    ι X (r • α) = r • ι X α
  ι_fMul : ∀ (X : VF) {p : ℕ} (f : Ω 0) (α : Ω (p + 1)),
    ι X (fMul f α) = fMul f (ι X α)
  ι_wedge1 : ∀ (X : VF) {p : ℕ} (ω : Ω 1) (α : Ω (p + 1)),
    ι X (wedge1 ω α) = fMul (ι X ω) α - wedge1 ω (ι X α)
  ι_squared : ∀ (X : VF) {p : ℕ} (α : Ω (p + 1 + 1)), ι X (ι X α) = 0
  ι_ι_anticomm : ∀ (X Y : VF) {p : ℕ} (α : Ω (p + 1 + 1)),
    ι X (ι Y α) = -(ι Y (ι X α))

  L_add : ∀ (X : VF) {p : ℕ} (α β : Ω p),
    L X (α + β) = L X α + L X β
  L_smul : ∀ (X : VF) {p : ℕ} (r : ℝ) (α : Ω p),
    L X (r • α) = r • L X α
  L_zero_eq_ι_d : ∀ (X : VF) (f : Ω 0), L X f = ι X (d f)
  L_comm_d : ∀ (X : VF) {p : ℕ} (α : Ω p), L X (d α) = d (L X α)
  L_fMul : ∀ (X : VF) {p : ℕ} (f : Ω 0) (α : Ω p),
    L X (fMul f α) = fMul (L X f) α + fMul f (L X α)
  ext_fdα : ∀ {p : ℕ} (T : Ω (p + 1) → Ω (p + 1)),
    (∀ (α β : Ω (p + 1)), T (α + β) = T α + T β) →
    (∀ (r : ℝ) (α : Ω (p + 1)), T (r • α) = r • T α) →
    (∀ (f : Ω 0) (α : Ω p), T (fMul f (d α)) = 0) →
    ∀ (β : Ω (p + 1)), T β = 0
  ι_one_form_nondegenerate : ∀ (α : Ω 1),
    (∀ (X : VF), ι X α = (0 : Ω 0)) → α = 0
  ι_two_form_nondegenerate : ∀ (ω : Ω 2),
    (∀ (X : VF), ι X ω = (0 : Ω 1)) → ω = 0

attribute [reducible, instance] DifferentialFormSpace.instAddCommGroup

attribute [reducible, instance] DifferentialFormSpace.instModule

/-- Provides a compatible $\mathbb{C}$-module structure on each $\Omega^p$ via scalar-tower with $\mathbb{R}$, used for complex-valued differential forms. -/
class HasComplexScalars (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  [instComplexModule : ∀ p, Module ℂ (Ω p)]
  [instScalarTower : ∀ p, IsScalarTower ℝ ℂ (Ω p)]
  [instSMulCommClass : ∀ p, SMulCommClass ℝ ℂ (Ω p)]

