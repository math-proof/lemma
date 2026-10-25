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
set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped Manifold ContDiff


/-- Differential $p$-forms on a smooth manifold $M$ (modeled on $E$ via `I`), realized
concretely as functions $M \to \Lambda^p E^*$ from points of $M$ to alternating $p$-forms
on the model space $E$. -/
@[reducible]
def ManifoldΩ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (_I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (p : ℕ) : Type _ :=
  M → (E [⋀^Fin p]→L[ℝ] ℝ)

/-- Vector fields on $M$ (modeled on $E$), realized concretely as functions $M \to E$
assigning to each point an element of the model space. -/
@[reducible]
def ManifoldVF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (_I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  M → E

