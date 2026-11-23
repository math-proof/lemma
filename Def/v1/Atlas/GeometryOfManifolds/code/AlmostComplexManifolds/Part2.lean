/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
public import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
public import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part2

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


/-- The space of almost complex structures compatible with the symplectic manifold $S$. -/
def CompatibleACS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) : Type _ :=
  { J : AlmostComplexStr (inst := inst) // IsCompatibleACS S J }


/-- The space of linear complex structures $J : V \to V$ compatible with a symplectic form $\omega$
on a finite-dimensional real vector space $V$. -/
def CompatibleComplexStructureSpace {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ω : LinearMap.BilinForm ℝ V) : Type _ :=
  { J : V →ₗ[ℝ] V // IsCompatibleComplexStr ω J }

