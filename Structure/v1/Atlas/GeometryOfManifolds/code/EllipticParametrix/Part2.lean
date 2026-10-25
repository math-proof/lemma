/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticParametrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Def.v1.Atlas.GeometryOfManifolds.code.EllipticParametrix.Part2
open ContinuousLinearMap Finset Manifold


/-- A smoothing operator $S$: bounded for each Sobolev norm with a one-step gain in regularity,
$\|S x\|_{s+1} \le C_s \|x\|_s$. -/
structure IsSmoothingOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sobolevNorm : ℕ → E → ℝ)
    (S : E →L[ℝ] E) where
  regularity_improvement : ∀ (s : ℕ), ∃ (C : ℝ), C > 0 ∧
    ∀ (x : E), sobolevNorm (s + 1) (S x) ≤ C * sobolevNorm s x


