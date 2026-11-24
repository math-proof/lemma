module
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
public import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
public import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Def.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
set_option autoImplicit false
open DifferentialFormSpace SymplecticLinearAlgebra


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


section Contractibility_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- At each point $x \in M$, the value $\omega_x$ of a pointwise symplectic form is a linear
symplectic form on the tangent space $T_xM$. -/
theorem pointwise_form_is_symplectic
    (ω : PointwiseSymplecticForm I M) (x : M) :
    IsSymplecticForm (ω.form x) := by
  constructor
  ·
    intro v
    have h := ω.skew x v v
    linarith
  ·
    intro v hv
    exact ω.nondeg x v hv

end Contractibility_Mathlib
