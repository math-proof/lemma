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
import Structure.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityBridge
set_option autoImplicit false


namespace EllipticRegularityBridge

/-- $\xi$ has Sobolev regularity $H^s$ iff $\|\xi\|_{H^s} < \infty$. -/
def HasSobolevRegularity {n k : ℕ} (snorms : SobolevNorms n k) (s : ℕ)
    (ξ : DiffForm n (k + 1)) : Prop :=
  ∃ (C : ℝ), snorms.norm s ξ ≤ C

end EllipticRegularityBridge
