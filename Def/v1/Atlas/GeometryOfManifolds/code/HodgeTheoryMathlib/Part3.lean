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
public import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib

@[expose] public section

set_option autoImplicit false


namespace HodgeMathlib

/-- The Hodge Laplacian $\Delta = dd^* + d^*d$ on differential forms. -/
noncomputable def laplacian {n : ℕ} (cod : Codifferential n)
    {k : ℕ} (α : DiffForm n (k + 1)) : DiffForm n (k + 1) :=
  dForm (cod.dstar α) + cod.dstar (dForm α)


/-- A form $\alpha$ is harmonic if $\Delta \alpha = 0$, i.e. it lies in the kernel of the Hodge Laplacian. -/
def IsHarmonic {n : ℕ} (cod : Codifferential n)
    {k : ℕ} (α : DiffForm n (k + 1)) : Prop :=
  laplacian cod α = 0


end HodgeMathlib
