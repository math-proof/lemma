/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeStarMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open scoped Manifold ComplexConjugate
open MeasureTheory
set_option autoImplicit false


noncomputable section

namespace HodgeStarMathlib

/-- A smooth complex-valued $k$-form on $M$ modelled on $\mathbb{C}^n$: a pointwise alternating
$\mathbb{C}$-multilinear $k$-form on $\mathbb{C}^n$. -/
def SmoothForm (n : ℕ) (M : Type*) [TopologicalSpace M] (k : ℕ) : Type _ :=
  M → (EuclideanSpace ℂ (Fin n)) [⋀^Fin k]→L[ℂ] ℂ

end HodgeStarMathlib
end
