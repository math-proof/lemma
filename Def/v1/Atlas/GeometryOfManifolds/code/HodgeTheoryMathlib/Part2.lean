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
import Instance.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib
set_option autoImplicit false


namespace HodgeMathlib

/-- The exterior derivative $d : \Omega^k \to \Omega^{k+1}$ on differential forms on Euclidean space. -/
noncomputable def dForm {n k : ℕ} (ω : DiffForm n k) : DiffForm n (k + 1) :=
  fun x => extDeriv ω x


end HodgeMathlib
