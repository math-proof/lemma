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
public import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part3

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


section ManifoldACS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The space of almost complex structures on $M$ compatible with the pointwise symplectic
form $\omega$ (Mathlib version). -/
def CompatibleACSSpace_Mathlib (ω : PointwiseSymplecticForm I M) : Type _ :=
  { J : AlmostComplexStructure I M // IsCompatibleACS_Mathlib I M ω J }

end ManifoldACS
