/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernFormGrading.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
open Bundle NormedSpace Matrix Complex


/-- A $\mathbb{C}$-algebra $R$ realizing the graded algebra of complex differential forms:
each $\Omega^p$ embeds $\mathbb{R}$-linearly into a homogeneous component of degree $p$ in
$R$, with an inverse extraction map. -/
structure ComplexDifferentialFormAlgebra
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R] where
  embed : ∀ (p : ℕ), Ω p → R
  embed_linear : ∀ (p : ℕ), ∀ (a b : Ω p) (c : ℝ),
    embed p (c • a + b) = (algebraMap ℝ R c) * embed p a + embed p b
  embed_homog : ∀ (p : ℕ) (α : Ω p), IsGradedFormAlgebra.IsHomog (embed p α) p
  extract : ∀ (p : ℕ), R → Ω p
  extract_embed : ∀ (p : ℕ) (α : Ω p), extract p (embed p α) = α

/-- All geometric data needed to define the Chern forms of a rank-$r$ vector bundle
$V \to M$ with connection $\nabla$: the connection, its curvature $R^\nabla$ (antisymmetric
in tangent vectors), an embedding of the form algebra into a $\mathbb{C}$-algebra $R$, the
$r \times r$ curvature matrix realised in $R$ (with each entry homogeneous of degree $2$),
and a "degree-$0$ scalar" hypothesis on the leading Chern scalar. -/
structure ChernFormGeometricData

    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E_mod : Type*) [NormedAddCommGroup E_mod] [NormedSpace 𝕜 E_mod]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E_mod H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]

    (r : ℕ)

    (Ω : ℕ → Type*) (VF : Type*) [DifferentialFormSpace Ω VF]

    (R : Type*) [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    where
  connection : CovariantDerivative I F V
  curvature : ∀ (x : M), TangentSpace I x → TangentSpace I x → (V x →L[𝕜] V x)
  curvature_antisymm : ∀ (x : M) (X Y : TangentSpace I x),
    curvature x X Y = -curvature x Y X
  formAlgebra : ComplexDifferentialFormAlgebra Ω VF R
  curvatureMatrix : Matrix (Fin r) (Fin r) R
  curvatureMatrix_deg2 : CurvatureMatrixDegreeTwo curvatureMatrix
  chernScalar_deg0 : ChernScalarHomogZero (R := R)

