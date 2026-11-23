/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import Mathlib.Analysis.Calculus.VectorField
public import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
public import Def.v1.Atlas.GeometryOfManifolds.code.OmitIndex
public import Def.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS
@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped Manifold ContDiff


section Instances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H]

variable (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]

variable [ChartedSpace H M]

/-- Pointwise addition gives the space of differential $p$-forms an abelian group structure. -/
noncomputable instance instAddCommGroupManifoldΩ (p : ℕ) :
    AddCommGroup (ManifoldΩ I M p) :=
  inferInstance

/-- Pointwise scalar multiplication gives differential $p$-forms an $\mathbb{R}$-module structure. -/
noncomputable instance instModuleManifoldΩ (p : ℕ) :
    Module ℝ (ManifoldΩ I M p) :=
  inferInstance

end Instances
