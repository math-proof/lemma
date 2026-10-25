/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityBridge.Part2
set_option autoImplicit false


namespace EllipticRegularityBridge

/-- Abstract data of Sobolev norms $\|\xi\|_{H^s}$ on $(k+1)$-forms, indexed by regularity $s$,
required to be nonnegative. -/
structure SobolevNorms (n k : ℕ) where
  norm : ℕ → DiffForm n (k + 1) → ℝ
  norm_nonneg : ∀ (s : ℕ) (ξ : DiffForm n (k + 1)), 0 ≤ norm s ξ

end EllipticRegularityBridge
