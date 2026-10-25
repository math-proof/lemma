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
import Def.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part5
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


section Submanifold_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Integrability of $J$**: the Nijenhuis tensor $N_J$ vanishes identically. By the
Newlander-Nirenberg theorem this is equivalent to $J$ coming from a genuine complex structure. -/
structure Integrable (J : AlmostComplexStructure I M)
    (N : ∀ x : M, TangentSpace I x → TangentSpace I x → TangentSpace I x) : Prop where
  vanishes : ∀ (x : M) (u v : TangentSpace I x), N x u v = 0

end Submanifold_Mathlib
