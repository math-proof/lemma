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
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib
set_option autoImplicit false


namespace HodgeMathlib

/-- Pointwise addition makes the space of differential $k$-forms an additive group. -/
noncomputable instance (n k : ℕ) : AddCommGroup (DiffForm n k) := Pi.addCommGroup

/-- Pointwise scalar multiplication makes the space of differential $k$-forms an $\mathbb{R}$-module. -/
noncomputable instance (n k : ℕ) : Module ℝ (DiffForm n k) := Pi.module _ _ _

/-- The product topology on the space of differential $k$-forms. -/
noncomputable instance (n k : ℕ) : TopologicalSpace (DiffForm n k) := Pi.topologicalSpace

end HodgeMathlib
