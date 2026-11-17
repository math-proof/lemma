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
public import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part2
@[expose] public section

set_option autoImplicit false


namespace HodgeMathlib

/-- A multi-index $\alpha = (\alpha_1, \dots, \alpha_n) \in \mathbb{N}^n$, indexing partial derivatives. -/
abbrev MultiIndex (n : ℕ) := Fin n →₀ ℕ

end HodgeMathlib
