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
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib

@[expose] public section

set_option autoImplicit false


namespace HodgeMathlib

/-- Pointwise addition makes the space of differential $k$-forms an additive group. -/
noncomputable instance (n k : ℕ) : AddCommGroup (DiffForm n k) := Pi.addCommGroup

/-- Pointwise scalar multiplication makes the space of differential $k$-forms an $\mathbb{R}$-module. -/
noncomputable instance (n k : ℕ) : Module ℝ (DiffForm n k) := Pi.module _ _ _

/-- The product topology on the space of differential $k$-forms. -/
noncomputable instance (n k : ℕ) : TopologicalSpace (DiffForm n k) := Pi.topologicalSpace

end HodgeMathlib
