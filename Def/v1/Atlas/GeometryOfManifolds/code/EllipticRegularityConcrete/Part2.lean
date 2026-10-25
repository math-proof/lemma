/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Instance.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityConcrete
set_option autoImplicit false


namespace EllipticRegularityConcrete

/-- A differential form is smooth ($C^\infty$) when its coefficient map is infinitely
differentiable as a function $\mathbb{R}^n \to (\mathbb{R}^n)^{[\Lambda^k]\to \mathbb{R}}$. -/
def IsSmoothForm {n k : ℕ} (ξ : DiffForm n k) : Prop :=
  ContDiff ℝ ⊤ ξ


end EllipticRegularityConcrete
