/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Interval
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part3
public section

set_option autoImplicit false


namespace HodgeMathlib

/-- An $L^2$ inner product on differential forms making $d^*$ the formal adjoint of $d$. -/
structure L2InnerProduct {n : ℕ} (cod : Codifferential n) where
  inner : ∀ {k : ℕ}, DiffForm n k → DiffForm n k → ℝ
  inner_self_eq_zero : ∀ {k : ℕ} (α : DiffForm n k), inner α α = 0 → α = 0
  inner_self_nonneg : ∀ {k : ℕ} (α : DiffForm n k), 0 ≤ inner α α
  inner_symm : ∀ {k : ℕ} (α β : DiffForm n k), inner α β = inner β α
  adjoint_d : ∀ {k : ℕ} (α : DiffForm n k) (β : DiffForm n (k + 1)),
    inner (dForm α) β = inner α (cod.dstar β)
  inner_add_left : ∀ {k : ℕ} (α β γ : DiffForm n k),
    inner (α + β) γ = inner α γ + inner β γ
  inner_smul_left : ∀ {k : ℕ} (r : ℝ) (α β : DiffForm n k),
    inner (r • α) β = r * inner α β


end HodgeMathlib
