/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFSVerify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ManifoldDFS

set_option autoImplicit false

open scoped Manifold ContDiff

/-- Sanity check: the manifold-`DifferentialFormSpace` instance is available for any smooth
manifold modelled on $(E, H, I)$. -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] :
    DifferentialFormSpace (ManifoldΩ I M) (ManifoldVF I M) :=
  instManifoldDFS I M

/-- Definitional check: the exterior derivative on $1$-forms in the DFS instance agrees with
`manifoldD`. -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (α : ManifoldΩ I M 1) :
    (instManifoldDFS I M).d α = manifoldD I α := rfl

/-- Definitional check: the exterior derivative on $0$-forms (functions) in the DFS instance is
`manifoldD`. -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (f : ManifoldΩ I M 0) :
    (instManifoldDFS I M).d f = manifoldD I f := rfl

/-- Definitional check: contraction $\iota_X \alpha$ on $2$-forms in the DFS instance agrees with
`manifoldIota`. -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (X : ManifoldVF I M)
    (α : ManifoldΩ I M 2) :
    (instManifoldDFS I M).ι X α = manifoldIota I X α := rfl

/-- Definitional check: Lie derivative $\mathcal{L}_X \alpha$ on $1$-forms in the DFS instance
agrees with `manifoldL`. -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (X : ManifoldVF I M)
    (α : ManifoldΩ I M 1) :
    (instManifoldDFS I M).L X α = manifoldL I X α := rfl

/-- Definitional check: the typeclass instance and the bundled `manifoldDFS` constructor agree. -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] :
    instManifoldDFS I M = manifoldDFS I M := rfl

/-- Sanity check: $d^2 = 0$ on smooth functions follows from the DFS axiom `d_squared`. -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (f : ManifoldΩ I M 0) :
    (instManifoldDFS I M).d ((instManifoldDFS I M).d f) = 0 :=
  (instManifoldDFS I M).d_squared f

/-- Sanity check: on functions, $\mathcal{L}_X f = \iota_X (df)$ (i.e. $\mathcal{L}_X f = X(f)$). -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (X : ManifoldVF I M) (f : ManifoldΩ I M 0) :
    (instManifoldDFS I M).L X f = (instManifoldDFS I M).ι X ((instManifoldDFS I M).d f) :=
  (instManifoldDFS I M).L_zero_eq_ι_d X f

/-- Definitional check: wedge product $\omega \wedge \alpha$ of two $1$-forms in the DFS instance
agrees with `manifoldWedge1`. -/
noncomputable example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (w : ManifoldΩ I M 1) (α : ManifoldΩ I M 1) :
    (instManifoldDFS I M).wedge1 w α = manifoldWedge1 I w α := rfl

/-- Concrete instantiation on $3$-manifolds: the DFS exterior derivative on $1$-forms reduces to
`manifoldD` definitionally. -/
noncomputable example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ M]
    (α : ManifoldΩ (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M 1) :
    (manifoldDFS (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M).d α =
    manifoldD (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) α := rfl
