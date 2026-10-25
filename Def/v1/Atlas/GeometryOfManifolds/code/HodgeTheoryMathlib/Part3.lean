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
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib
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
