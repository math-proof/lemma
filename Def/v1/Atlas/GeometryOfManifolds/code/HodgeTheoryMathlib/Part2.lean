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
public import Instance.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib

@[expose] public section

set_option autoImplicit false


namespace HodgeMathlib

/-- The exterior derivative $d : \Omega^k \to \Omega^{k+1}$ on differential forms on Euclidean space. -/
noncomputable def dForm {n k : ℕ} (ω : DiffForm n k) : DiffForm n (k + 1) :=
  fun x => extDeriv ω x


end HodgeMathlib
