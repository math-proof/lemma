/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernClassProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.LinearAlgebra.Orientation
import Def.v1.Atlas.GeometryOfManifolds.code.ChernClassProperties
set_option autoImplicit false

open SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]


/-- Data certifying that the manifold $M$ is compact, oriented, of even real dimension $2 \dim$,
and carries a non-exact volume form. -/
structure IsCompactOriented
    {EModel : Type*} [NormedAddCommGroup EModel] [NormedSpace ℝ EModel]
    {HModel : Type*} [TopologicalSpace HModel]
    (I : ModelWithCorners ℝ EModel HModel)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HModel M]
    [IsManifold I ⊤ M] [CompactSpace M]
    (Ω : ℕ → Type*) [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    (d : ∀ {p : ℕ}, Ω p → Ω (p + 1)) where
  dim : ℕ
  dim_pos : 0 < dim
  orientation : Orientation ℝ EModel (Fin (2 * dim))
  vol : Ω (2 * dim - 1 + 1)
  vol_not_exact : ¬ (∃ β : Ω (2 * dim - 1), d β = vol)

/-- An abstract notion of integrality of de Rham cohomology classes: a predicate `isIntegral` on
forms closed under sums and negation, with $0$ integral and integral forms automatically closed. -/
structure IsIntegralCohomologyClass
    (Ω : ℕ → Type*) [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    (d : ∀ {p : ℕ}, Ω p → Ω (p + 1)) where
  isIntegral : {k : ℕ} → Ω k → Prop
  integral_closed : ∀ {k : ℕ} (α : Ω k), isIntegral α → d α = 0
  integral_zero : ∀ (k : ℕ), isIntegral (0 : Ω k)
  integral_add : ∀ {k : ℕ} (α β : Ω k), isIntegral α → isIntegral β → isIntegral (α + β)
  integral_neg : ∀ {k : ℕ} (α : Ω k), isIntegral α → isIntegral (-α)

/-- Data packaging a complex vector bundle $E \to M$ of rank $r$ with a connection and curvature
matrix, plus the Chern–Weil machinery (`embed`, `extract`, `chernWeilParam`) producing the
top Chern form $c_r(E, \nabla)$ as an integral cohomology class. -/
structure ComplexVectorBundleData
    {EModel : Type*} [NormedAddCommGroup EModel] [NormedSpace ℝ EModel]
    {HModel : Type*} [TopologicalSpace HModel]
    (I : ModelWithCorners ℝ EModel HModel)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HModel M] [IsManifold I ⊤ M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (E : M → Type*) [TopologicalSpace (Bundle.TotalSpace F E)]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle ℂ F E]
    (Ω : ℕ → Type*) [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    (d : ∀ {p : ℕ}, Ω p → Ω (p + 1))
    (d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0)
    (intCoh : IsIntegralCohomologyClass Ω d)
    (r : ℕ) (totalAlg : Type*) [CommRing totalAlg] where
  rank_pos : 0 < r
  connectionForm : Ω 1
  curvatureRep : Ω 2
  curvature_eq : d connectionForm = curvatureRep
  curvatureMatrix : Matrix (Fin r) (Fin r) (Ω 2)
  curvatureMatrix_closed : ∀ i j, d (curvatureMatrix i j) = 0
  embed : Ω 2 → totalAlg
  extract : totalAlg → Ω (2 * r - 1 + 1)
  chernWeilParam : totalAlg
  embed_add : ∀ (a b : Ω 2), embed (a + b) = embed a + embed b
  extract_add : ∀ (a b : totalAlg), extract (a + b) = extract a + extract b
  extract_one : extract 1 = 0
  chernWeil_zero :
    extract (totalChernForm
      ((0 : Matrix (Fin r) (Fin r) (Ω 2)).map embed) chernWeilParam) = 0
  chernWeil_closed :
    ∀ (A : Matrix (Fin r) (Fin r) (Ω 2)),
      (∀ i j, d (A i j) = 0) →
      d (extract (totalChernForm (A.map embed) chernWeilParam)) = 0
  chernWeil_smul :
    ∀ (c : ℝ) (A : Matrix (Fin r) (Fin r) (Ω 2)),
      extract (totalChernForm ((c • A).map embed) chernWeilParam) =
      c ^ r • extract (totalChernForm (A.map embed) chernWeilParam)
  chernWeil_nontrivial :
    ∃ (A : Matrix (Fin r) (Fin r) (Ω 2)),
      extract (totalChernForm (A.map embed) chernWeilParam) ≠ 0
  chernWeil_perm :
    ∀ (σ : Equiv.Perm (Fin r)) (A : Matrix (Fin r) (Fin r) (Ω 2)),
      extract (totalChernForm ((A.submatrix σ σ).map embed) chernWeilParam) =
      extract (totalChernForm (A.map embed) chernWeilParam)
  chernWeil_alternating :
    ∀ (A : Matrix (Fin r) (Fin r) (Ω 2)) (i j : Fin r),
      i ≠ j → (∀ k, A i k = A j k) →
      extract (totalChernForm (A.map embed) chernWeilParam) = 0
  topChernRep_integral :
    intCoh.isIntegral
      (extract (totalChernForm (curvatureMatrix.map embed) chernWeilParam))

/-- Data carrying a representative of the Euler class $e(E) \in H^{2r}(M, \mathbb{Z})$ via the
Pfaffian of the curvature matrix, together with the signed count of zeros of a generic section. -/
structure EulerClassData
    (Ω : ℕ → Type*) [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
    (d : ∀ {p : ℕ}, Ω p → Ω (p + 1))
    (intCoh : IsIntegralCohomologyClass Ω d)
    (r : ℕ)
    (curvatureMatrix : Matrix (Fin r) (Fin r) (Ω 2)) where
  pfaffianMap : Matrix (Fin r) (Fin r) (Ω 2) → Ω (2 * r - 1 + 1)
  eulerRep : Ω (2 * r - 1 + 1)
  eulerRep_eq_pfaffian : eulerRep = pfaffianMap curvatureMatrix
  eulerRep_closed : d eulerRep = 0
  pfaffian_zero : pfaffianMap 0 = 0
  pfaffian_homogeneous : ∀ (c : ℝ) (A : Matrix (Fin r) (Fin r) (Ω 2)),
    pfaffianMap (c • A) = c ^ r • pfaffianMap A
  pfaffian_closed : ∀ (A : Matrix (Fin r) (Fin r) (Ω 2)),
    (∀ i j, d (A i j) = 0) → d (pfaffianMap A) = 0
  eulerRep_integral : intCoh.isIntegral eulerRep
  sectionZeroCount : ℤ
  sectionZeroCount_spec :
    curvatureMatrix = 0 → sectionZeroCount = 0

