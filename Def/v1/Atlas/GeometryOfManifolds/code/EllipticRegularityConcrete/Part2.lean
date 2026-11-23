/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Instance.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityConcrete

@[expose] public section

set_option autoImplicit false


namespace EllipticRegularityConcrete

/-- A differential form is smooth ($C^\infty$) when its coefficient map is infinitely
differentiable as a function $\mathbb{R}^n \to (\mathbb{R}^n)^{[\Lambda^k]\to \mathbb{R}}$. -/
def IsSmoothForm {n k : ℕ} (ξ : DiffForm n k) : Prop :=
  ContDiff ℝ ⊤ ξ


end EllipticRegularityConcrete
