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
public import Structure.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityConcrete

@[expose] public section

set_option autoImplicit false


namespace EllipticRegularityConcrete

/-- The form $\xi$ has Sobolev regularity of order $s$ when $\|\xi\|_s$ is bounded by some
constant. (Trivially holds in this framework but records the membership in $H^s$ qualitatively.) -/
def HasSobolevRegularity {n k : ℕ} (snorms : SobolevNorms n k) (s : ℕ)
    (ξ : DiffForm n (k + 1)) : Prop :=
  ∃ (C : ℝ), snorms.norm s ξ ≤ C


end EllipticRegularityConcrete
