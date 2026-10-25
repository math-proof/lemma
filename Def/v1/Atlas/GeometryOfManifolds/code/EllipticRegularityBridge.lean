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
set_option autoImplicit false


namespace EllipticRegularityBridge

/-- Differential $k$-form on $\mathbb{R}^n$: a pointwise alternating $\mathbb{R}$-multilinear
$k$-form on $\mathbb{R}^n$. -/
def DiffForm (n k : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ

end EllipticRegularityBridge
