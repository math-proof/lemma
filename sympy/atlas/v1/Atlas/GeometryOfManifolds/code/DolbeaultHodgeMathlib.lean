/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open ContinuousAlternatingMap

namespace DolbeaultHodgeMathlib

/-- The space $\Omega^k(\mathbb{R}^n)$ of (continuous) differential $k$-forms on Euclidean
$n$-space, modelled as maps from points to continuous alternating $k$-linear forms. -/
def DiffForm (n k : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ

/-- Pointwise additive group structure on $k$-forms. -/
noncomputable instance instAddCommGroup (n k : ℕ) : AddCommGroup (DiffForm n k) :=
  Pi.addCommGroup
/-- Pointwise $\mathbb{R}$-module structure on $k$-forms. -/
noncomputable instance instModule (n k : ℕ) : Module ℝ (DiffForm n k) :=
  Pi.module _ _ _

/-- Axiomatic $L^2$ inner product on differential forms of each degree, satisfying
positivity, symmetry, and bilinearity. -/
structure L2InnerProduct (n : ℕ) where
  inner : ∀ {k : ℕ}, DiffForm n k → DiffForm n k → ℝ
  inner_self_eq_zero : ∀ {k : ℕ} (α : DiffForm n k), inner α α = 0 → α = 0
  inner_self_nonneg : ∀ {k : ℕ} (α : DiffForm n k), 0 ≤ inner α α
  inner_symm : ∀ {k : ℕ} (α β : DiffForm n k), inner α β = inner β α
  inner_add_left : ∀ {k : ℕ} (α β γ : DiffForm n k),
    inner (α + β) γ = inner α γ + inner β γ
  inner_smul_left : ∀ {k : ℕ} (r : ℝ) (α β : DiffForm n k),
    inner (r • α) β = r * inner α β


/-- Mathlib `Inner` instance built from the axiomatic $L^2$ inner product. -/
@[reducible]
def L2InnerProduct.toInner {n : ℕ} (ip : L2InnerProduct n) (k : ℕ) :
    Inner ℝ (DiffForm n k) where
  inner := ip.inner

/-- Build a `PreInnerProductSpace.Core` from an `L2InnerProduct`, giving access to Mathlib's
inner-product-space machinery. -/
@[reducible]
noncomputable def L2InnerProduct.toPreCore {n : ℕ} (ip : L2InnerProduct n) (k : ℕ) :
    PreInnerProductSpace.Core ℝ (DiffForm n k) where
  inner := ip.inner
  conj_inner_symm x y := by
    change ip.inner y x = ip.inner x y
    exact ip.inner_symm y x
  re_inner_nonneg x := by
    change 0 ≤ ip.inner x x
    exact ip.inner_self_nonneg x
  add_left x y z := ip.inner_add_left x y z
  smul_left x y r := by
    change ip.inner (r • x) y = r * ip.inner x y
    exact ip.inner_smul_left r x y

/-- The seminormed group structure on $\Omega^k$ induced by the $L^2$ inner product. -/
@[reducible]
noncomputable def L2InnerProduct.toSeminormedAddCommGroup {n : ℕ}
    (ip : L2InnerProduct n) (k : ℕ) : SeminormedAddCommGroup (DiffForm n k) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ (DiffForm n k) _ _ _ (ip.toPreCore k)

/-- The Mathlib `InnerProductSpace` structure on $\Omega^k$ induced by the $L^2$ inner product. -/
@[reducible]
noncomputable def L2InnerProduct.toInnerProductSpace {n : ℕ}
    (ip : L2InnerProduct n) (k : ℕ) :
    @InnerProductSpace ℝ (DiffForm n k) _
      (ip.toSeminormedAddCommGroup k) :=
  @InnerProductSpace.ofCore ℝ (DiffForm n k) _ _ _ (ip.toPreCore k)

/-- Axiomatic Dolbeault data: the operators $\bar\partial$, its formal adjoint $\bar\partial^*$,
and the $\bar\partial$-Laplacian $\bar\square = \bar\partial \bar\partial^* + \bar\partial^*
\bar\partial$, satisfying $\bar\partial^2 = 0$ and linearity. -/
structure DolbeaultData (n : ℕ) where
  delbar : ∀ {k : ℕ}, DiffForm n k → DiffForm n (k + 1)
  delbar_star : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n k
  box_bar : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  delbar_sq : ∀ {k : ℕ} (α : DiffForm n k), delbar (delbar α) = 0
  delbar_add : ∀ {k : ℕ} (α β : DiffForm n k), delbar (α + β) = delbar α + delbar β
  delbar_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n k), delbar (r • α) = r • delbar α
  box_bar_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)),
    box_bar α = delbar (delbar_star α) + delbar_star (delbar α)
  delbar_star_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)),
    delbar_star (r • α) = r • delbar_star α

/-- The adjointness relation $\langle \bar\partial \alpha, \beta \rangle = \langle \alpha,
\bar\partial^* \beta \rangle$ between $\bar\partial$ and $\bar\partial^*$. -/
structure HasDelbarAdjoint {n : ℕ} (ip : L2InnerProduct n) (dol : DolbeaultData n) : Prop where
  adj : ∀ {k : ℕ} (α : DiffForm n k) (β : DiffForm n (k + 1)),
    ip.inner (dol.delbar α) β = ip.inner α (dol.delbar_star β)
