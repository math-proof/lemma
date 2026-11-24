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
public import Theorem.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part2
set_option autoImplicit false
open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace WeinsteinNeighborhood

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Linear Lagrangian normal bundle identification.** For $E$ a Lagrangian subspace
of a symplectic vector space $(V, \Omega)$, there is a natural linear isomorphism
$V/E \xrightarrow{\sim} E^*$, identifying the "normal space" to $E$ with $T^*E$. -/
noncomputable def lagrangianQuotientDualEquiv [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    (V ⧸ E) ≃ₗ[ℝ] Dual ℝ E :=
  LinearMap.linearEquivOfInjective
    (quotientToDual hΩ hE)
    (quotientToDual_injective hΩ hE)
    (quotient_finrank_eq_dual hΩ hE)

end WeinsteinNeighborhood
