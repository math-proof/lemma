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
public import Def.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityBridge

@[expose] public section

set_option autoImplicit false


namespace EllipticRegularityBridge

/-- Pointwise additive group structure on differential $k$-forms. -/
noncomputable instance instAddCommGroup (n k : ℕ) : AddCommGroup (DiffForm n k) :=
  Pi.addCommGroup

/-- Pointwise $\mathbb{R}$-module structure on differential $k$-forms. -/
noncomputable instance instModule (n k : ℕ) : Module ℝ (DiffForm n k) :=
  Pi.module _ _ _

/-- Borel measurable space structure on $\mathbb{R}^n$, needed for integration of forms. -/
noncomputable instance instMeasurableSpace (n : ℕ) :
    MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _

end EllipticRegularityBridge
