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
import Def.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part3
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


section ManifoldACS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- An **almost complex structure** on a smooth manifold $M$ in Mathlib formalism: a smooth
field of fiberwise endomorphisms $J_x : T_xM \to T_xM$ with $J_x^2 = -\mathrm{id}$. -/
structure AlmostComplexStructure where
  J : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x
  sq_neg : ∀ (x : M) (v : TangentSpace I x), (J x) ((J x) v) = -v

/-- A **pointwise symplectic form** on $M$: a field of skew-symmetric, nondegenerate bilinear
forms $\omega_x : T_xM \times T_xM \to \mathbb{R}$ (closedness is not yet imposed). -/
structure PointwiseSymplecticForm where
  form : ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ
  skew : ∀ (x : M) (u v : TangentSpace I x), form x u v = -(form x v u)
  nondeg : ∀ (x : M) (u : TangentSpace I x), (∀ v, form x u v = 0) → u = 0

/-- $J$ is **compatible** with the pointwise symplectic form $\omega$ in Mathlib formalism:
$\omega(Ju, Jv) = \omega(u, v)$ and $\omega(v, Jv) > 0$ for $v \neq 0$ (taming/positivity). -/
structure IsCompatibleACS_Mathlib (ω : PointwiseSymplecticForm I M)
    (J : AlmostComplexStructure I M) : Prop where
  preserves : ∀ (x : M) (u v : TangentSpace I x),
    ω.form x ((J.J x) u) ((J.J x) v) = ω.form x u v
  taming : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
    ω.form x v ((J.J x) v) > 0

end ManifoldACS
