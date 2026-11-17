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
public import Structure.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityBridge

@[expose] public section

set_option autoImplicit false


namespace EllipticRegularityBridge

/-- $\xi$ has Sobolev regularity $H^s$ iff $\|\xi\|_{H^s} < \infty$. -/
def HasSobolevRegularity {n k : ℕ} (snorms : SobolevNorms n k) (s : ℕ)
    (ξ : DiffForm n (k + 1)) : Prop :=
  ∃ (C : ℝ), snorms.norm s ξ ≤ C

end EllipticRegularityBridge
