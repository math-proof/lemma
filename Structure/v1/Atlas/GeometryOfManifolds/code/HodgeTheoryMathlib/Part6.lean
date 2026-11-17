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
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part6
public section

set_option autoImplicit false


namespace HodgeMathlib

/-- $L$ is Fredholm: there is a left parametrix $P$ with $PL = I + S_{\mathrm{left}}$, and the kernel of $L$ is finite-dimensional. -/
structure IsFredholm {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  P : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  S_left : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  PL_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), P (L α) = α + S_left α
  ker_contained : ∀ {k : ℕ} (α : DiffForm n (k + 1)),
    L α = 0 → α + S_left α = P (0 : DiffForm n (k + 1))
  L_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)), L (α + β) = L α + L β
  L_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)), L (r • α) = r • L α


end HodgeMathlib
