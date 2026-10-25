/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Mathlib.Analysis.Calculus.VectorField
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Def.v1.Atlas.GeometryOfManifolds.code.OmitIndex
import Def.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS
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
