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
public import Class.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib
public section

set_option autoImplicit false


namespace HodgeMathlib

/-- Every elliptic operator on differential forms admits a parametrix. -/
structure HasGreenOperatorDecomp {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  G : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  H : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  H_maps_to_ker : ∀ {k : ℕ} (α : DiffForm n (k + 1)), L (H α) = 0
  LG_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), L (G α) = α + -(H α)
  GL_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), G (L α) = α + -(H α)
  H_idem : ∀ {k : ℕ} (α : DiffForm n (k + 1)), H (H α) = H α


end HodgeMathlib
