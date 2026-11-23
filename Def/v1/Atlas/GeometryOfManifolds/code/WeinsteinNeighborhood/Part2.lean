/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
public import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.ODE.PicardLindelof
public import Theorem.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood

@[expose] public section

set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


namespace WeinsteinNeighborhood

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- For $E \subseteq V$ Lagrangian, the descent of `symplecticToDual Ω E` to
a linear map $V/E \to E^*$ given by $[v] \mapsto \Omega(v, \cdot)|_E$. -/
noncomputable def quotientToDual [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    (V ⧸ E) →ₗ[ℝ] Dual ℝ E :=
  E.liftQ (symplecticToDual Ω E) (lagrangian_le_ker hΩ hE)

end WeinsteinNeighborhood
