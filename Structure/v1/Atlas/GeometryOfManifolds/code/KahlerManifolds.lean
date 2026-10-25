/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.IsManifold.Basic
set_option autoImplicit false


noncomputable section

open scoped Manifold


section MfdKahler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- A symplectic form on a manifold: a smoothly varying nondegenerate antisymmetric bilinear form $\omega_x$ on each tangent space $T_x M$. -/
structure SymplecticFormOnMfd
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  ω : ∀ (x : M), TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  antisymm : ∀ (x : M) (u v : TangentSpace I x), ω x u v = -(ω x v u)
  nondegenerate : ∀ (x : M) (u : TangentSpace I x),
    (∀ v : TangentSpace I x, ω x u v = 0) → u = 0
  closed : True

end MfdKahler
end
