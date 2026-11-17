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
public import Def.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityConcrete.Part2
public section

set_option autoImplicit false


namespace EllipticRegularityConcrete

/-- A family of nonnegative Sobolev seminorms indexed by regularity index $s \in \mathbb{N}$,
acting on differential $(k+1)$-forms. -/
structure SobolevNorms (n k : ℕ) where
  norm : ℕ → DiffForm n (k + 1) → ℝ
  norm_nonneg : ∀ (s : ℕ) (ξ : DiffForm n (k + 1)), 0 ≤ norm s ξ

end EllipticRegularityConcrete
