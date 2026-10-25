/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.ODE.PicardLindelof
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


namespace WeinsteinNeighborhood

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The linear map $V \to E^*$ sending $v \mapsto (e \mapsto \Omega(v, e))$,
where $\Omega$ is a bilinear form on $V$ and $E \subseteq V$ a subspace. -/
noncomputable def symplecticToDual (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) :
    V →ₗ[ℝ] Dual ℝ E where
  toFun v := {
    toFun := fun e => Ω v (e : V)
    map_add' := by intro e₁ e₂; simp [map_add]
    map_smul' := by intro r e; simp [map_smul]
  }
  map_add' := by intro v w; ext e; simp [map_add, LinearMap.add_apply]
  map_smul' := by intro r v; ext e; simp [map_smul, LinearMap.smul_apply]

end WeinsteinNeighborhood
