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
public import Def.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace

public section

namespace WeinsteinNeighborhood

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The kernel of `symplecticToDual Ω E` is the symplectic orthogonal complement
$E^{\perp_\Omega} = \{v \in V : \Omega(v, e) = 0 \text{ for all } e \in E\}$. -/
lemma symplecticToDual_ker [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    (E : Submodule ℝ V) :
    LinearMap.ker (symplecticToDual Ω E) = symplecticOrtho Ω E := by
  ext v
  simp only [LinearMap.mem_ker, symplecticOrtho]
  constructor
  · intro hv u hu
    have : (symplecticToDual Ω E v) ⟨u, hu⟩ = 0 := by rw [hv]; rfl
    simp [symplecticToDual] at this
    exact hΩ.alt.isRefl v u this
  · intro hv
    ext ⟨e, he⟩
    simp [symplecticToDual]
    exact hΩ.alt.isRefl e v (hv e he)

/-- A Lagrangian subspace $E$ is contained in the kernel of `symplecticToDual Ω E`,
since $E = E^{\perp_\Omega}$. -/
lemma lagrangian_le_ker [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    E ≤ LinearMap.ker (symplecticToDual Ω E) := by
  rw [symplecticToDual_ker hΩ]
  unfold IsLagrangian at hE
  rw [hE]

end WeinsteinNeighborhood
