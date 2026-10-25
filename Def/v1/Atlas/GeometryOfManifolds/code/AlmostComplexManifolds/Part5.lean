/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Theorem.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part2
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


section Contractibility_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Fiberwise contractibility in Mathlib formalism: at each $x \in M$, the space of linear
complex structures compatible with $\omega_x$ is contractible. -/
@[reducible]
noncomputable def fiberwise_acs_contractible_Mathlib
    [hfd : FiniteDimensional ℝ E]
    (ω : PointwiseSymplecticForm I M) (x : M) :
    letI : FiniteDimensional ℝ (TangentSpace I x) := hfd
    IsContractible (CompatibleComplexStructureSpace (ω.form x)) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := hfd
  exact fiberwise_acs_contractible (pointwise_form_is_symplectic ω x)

end Contractibility_Mathlib
