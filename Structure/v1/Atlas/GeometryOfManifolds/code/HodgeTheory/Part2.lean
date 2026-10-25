/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- The $L^2$ inner product on differential forms: a symmetric, positive-definite,
$\mathbb{R}$-bilinear form $\langle \cdot, \cdot \rangle$ on each $\Omega^p$ for which
$d$ and $d^*$ are mutually adjoint, i.e. $\langle d\alpha, \beta\rangle = \langle \alpha, d^*\beta\rangle$. -/
structure L2InnerProduct
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) where
  inner : ∀ {p : ℕ}, Ω p → Ω p → ℝ
  inner_self_eq_zero : ∀ {p : ℕ} (α : Ω p), inner α α = 0 → α = 0
  inner_self_nonneg : ∀ {p : ℕ} (α : Ω p), 0 ≤ inner α α
  inner_symm : ∀ {p : ℕ} (α β : Ω p), inner α β = inner β α
  adjoint_d : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (inst.d α) β = inner α (cod.dstar β)
  inner_add_left : ∀ {p : ℕ} (α β γ : Ω p),
    inner (α + β) γ = inner α γ + inner β γ
  inner_smul_left : ∀ {p : ℕ} (r : ℝ) (α β : Ω p),
    inner (r • α) β = r * inner α β


