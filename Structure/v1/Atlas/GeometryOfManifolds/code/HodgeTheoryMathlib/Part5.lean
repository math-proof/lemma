/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Class.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib
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
