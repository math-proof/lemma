/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernClassProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.LinearAlgebra.Orientation
set_option autoImplicit false

open SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]


/-- The intertwiner $T = \tfrac{1}{2}(\mathrm{id} - J_1 J_0)$ between two complex structures
$J_0, J_1$ on $V$, satisfying $T \circ J_0 = J_1 \circ T$. -/
noncomputable def complexStrIntertwiner (J₀ J₁ : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (1/2 : ℝ) • (LinearMap.id - J₁.comp J₀)

/-- A representative of the first Chern class $c_1(L) = \tfrac{1}{2\pi} R^\nabla$ obtained from a
curvature 2-form. -/
noncomputable def firstChernClassRepManifold (curvature : Ω₂) : Ω₂ :=
  (1 / (2 * Real.pi)) • curvature

