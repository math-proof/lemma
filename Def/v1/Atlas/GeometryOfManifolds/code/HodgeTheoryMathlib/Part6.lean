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
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part5
set_option autoImplicit false


namespace HodgeMathlib

/-- Hodge theorem: every closed form $\alpha$ is cohomologous to a unique harmonic representative $h$, i.e. $\alpha = h + d\beta$. -/
def IsSmoothForm {n k : ℕ} (ξ : DiffForm n k) : Prop :=
  ContDiff ℝ ⊤ ξ


end HodgeMathlib
