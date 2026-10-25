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
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part6
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
