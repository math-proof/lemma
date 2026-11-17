/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityBridge.lean -/

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
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Def.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityBridge.Part2
public section

set_option autoImplicit false


namespace EllipticRegularityBridge

/-- Abstract data of Sobolev norms $\|\xi\|_{H^s}$ on $(k+1)$-forms, indexed by regularity $s$,
required to be nonnegative. -/
structure SobolevNorms (n k : ℕ) where
  norm : ℕ → DiffForm n (k + 1) → ℝ
  norm_nonneg : ∀ (s : ℕ) (ξ : DiffForm n (k + 1)), 0 ≤ norm s ξ

end EllipticRegularityBridge
