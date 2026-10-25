/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernFormGrading.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ChernFormGrading
open Bundle NormedSpace Matrix Complex


/-- The **total Chern form** of $(E, \nabla)$:
$$c(E, \nabla) = \det\!\left(I + \frac{i}{2\pi} R^\nabla\right) \in \Omega^\bullet(M, \mathbb{C}),$$
defined via the curvature matrix and the appropriate scalar normalization. -/
noncomputable def totalChernFormGeometric
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E_mod : Type*} [NormedAddCommGroup E_mod] [NormedSpace 𝕜 E_mod]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E_mod H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]
    {r : ℕ}
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    (data : ChernFormGeometricData 𝕜 E_mod H I M F V r Ω VF R) : R :=
  totalChernFormWithScalar data.curvatureMatrix

/-- The **$j$-th Chern form** $c_j(E, \nabla) \in \Omega^{2j}(M, \mathbb{C})$, obtained as
the degree-$2j$ component of the total Chern form
$\det(I + \frac{i}{2\pi} R^\nabla) = \sum_j c_j$. -/
noncomputable def chernFormDegree
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E_mod : Type*} [NormedAddCommGroup E_mod] [NormedSpace 𝕜 E_mod]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E_mod H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]
    {r : ℕ}
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    (data : ChernFormGeometricData 𝕜 E_mod H I M F V r Ω VF R)
    (j : ℕ) : R :=
  chernClassWithScalar data.curvatureMatrix j

