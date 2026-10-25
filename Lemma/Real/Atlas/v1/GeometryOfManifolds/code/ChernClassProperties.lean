import Mathlib
import sympy.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.ChernClassProperties.Part2
open SymplecticLinearAlgebra


/--
[complexStr_intertwiner_commutes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernClassProperties.lean)
-/
@[path]
lemma complexStr_intertwiner_commutes
  [AddCommGroup V]
  [Module ℝ V]
  {J₀ J₁ : V →ₗ[ℝ] V}
-- given
  (hJ₀ : IsComplexStructure J₀)
  (hJ₁ : IsComplexStructure J₁) :
-- imply
  (complexStrIntertwiner J₀ J₁).comp J₀ = J₁.comp (complexStrIntertwiner J₀ J₁) := by
-- proof
  ext v
  simp only [complexStrIntertwiner, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  rw [map_smul]
  congr 1
  have hJ₀v : J₀ (J₀ v) = -v := hJ₀.apply_apply v
  have hJ₁J₀v : J₁ (J₁ (J₀ v)) = -(J₀ v) := hJ₁.apply_apply (J₀ v)
  rw [hJ₀v, map_neg, map_sub, hJ₁J₀v]
  abel
section TensorAdditivity
variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
variable {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H₀ M]
variable (Ω₂ : Type*) [AddCommGroup Ω₂] [Module ℝ Ω₂]

/--
[firstChernClass_tensor_product_additivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernClassProperties.lean)
-/
@[path]
lemma firstChernClass_tensor_product_additivity
  [AddCommGroup V]
  [Module ℝ V]
  [NormedAddCommGroup E₀]
  [NormedSpace ℝ E₀]
  [TopologicalSpace H₀]
  {I₀ : ModelWithCorners ℝ E₀ H₀}
  [TopologicalSpace M]
  [ChartedSpace H₀ M]
  {Ω₂ : Type*}
  [AddCommGroup Ω₂]
  [Module ℝ Ω₂]
  {R_L R_L' : Ω₂} :
-- imply
  firstChernClassRepManifold Ω₂ (R_L + R_L') = firstChernClassRepManifold Ω₂ R_L + firstChernClassRepManifold Ω₂ R_L' := by
-- proof
  simp only [firstChernClassRepManifold]
  exact smul_add _ R_L R_L'
end TensorAdditivity
section TopChernEuler
variable {EModel : Type*} [NormedAddCommGroup EModel] [NormedSpace ℝ EModel]
variable {HModel : Type*} [TopologicalSpace HModel]
variable {I : ModelWithCorners ℝ EModel HModel}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace HModel M] [IsManifold I ⊤ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {E : M → Type*} [TopologicalSpace (Bundle.TotalSpace F E)]
variable [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
variable [∀ x, TopologicalSpace (E x)]
variable [FiberBundle F E] [VectorBundle ℂ F E]
variable {Ω : ℕ → Type*} [∀ p, AddCommGroup (Ω p)] [∀ p, Module ℝ (Ω p)]
variable {d : ∀ {p : ℕ}, Ω p → Ω (p + 1)}
variable {d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0}
variable {r : ℕ} {totalAlg : Type*} [CommRing totalAlg]

/--
[EulerClassData.eulerRep_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernClassProperties.lean)
-/
@[path]
lemma EulerClassData.eulerRep_trivial
  [AddCommGroup V]
  [Module ℝ V]
  [NormedAddCommGroup EModel]
  [NormedSpace ℝ EModel]
  [TopologicalSpace HModel]
  {I : ModelWithCorners ℝ EModel HModel}
  [TopologicalSpace M]
  [ChartedSpace HModel M]
  [IsManifold I ⊤ M]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {E : M → Type*}
  [TopologicalSpace (Bundle.TotalSpace F E)]
  [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E]
  [VectorBundle ℂ F E]
  {Ω : ℕ → Type*}
  [∀ p, AddCommGroup (Ω p)]
  [∀ p, Module ℝ (Ω p)]
  {d : ∀ {p : ℕ}, Ω p → Ω (p + 1)}
  {d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0}
  {r : ℕ}
  [CommRing totalAlg]
  {Ω : ℕ → Type*}
  [∀ p, AddCommGroup (Ω p)]
  [∀ p, Module ℝ (Ω p)]
  {d : ∀ {p : ℕ}, Ω p → Ω (p + 1)}
  {intCoh : IsIntegralCohomologyClass Ω d}
  {r : ℕ}
  {curvatureMatrix : Matrix (Fin r) (Fin r) (Ω 2)}
  {euler : EulerClassData Ω d intCoh r curvatureMatrix}
-- given
  (h : curvatureMatrix = 0) :
-- imply
  euler.eulerRep = 0 := by
-- proof
  subst h
  rw [euler.eulerRep_eq_pfaffian, euler.pfaffian_zero]

/--
[ComplexVectorBundleData.topChernRep_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernClassProperties.lean)
-/
@[path]
lemma ComplexVectorBundleData.topChernRep_closed
  [AddCommGroup V]
  [Module ℝ V]
  [NormedAddCommGroup EModel]
  [NormedSpace ℝ EModel]
  [TopologicalSpace HModel]
  {I : ModelWithCorners ℝ EModel HModel}
  [TopologicalSpace M]
  [ChartedSpace HModel M]
  [IsManifold I ⊤ M]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {E : M → Type*}
  [TopologicalSpace (Bundle.TotalSpace F E)]
  [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E]
  [VectorBundle ℂ F E]
  {Ω : ℕ → Type*}
  [∀ p, AddCommGroup (Ω p)]
  [∀ p, Module ℝ (Ω p)]
  {d : ∀ {p : ℕ}, Ω p → Ω (p + 1)}
  {d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0}
  {r : ℕ}
  [CommRing totalAlg]
  {intCoh : IsIntegralCohomologyClass Ω d}
  {bundle : ComplexVectorBundleData I M F E Ω d d_squared intCoh r totalAlg} :
-- imply
  d bundle.topChernRep = 0 := by
-- proof
  simp only [ComplexVectorBundleData.topChernRep, ComplexVectorBundleData.chernWeilMapDef]
  exact bundle.chernWeil_closed bundle.curvatureMatrix bundle.curvatureMatrix_closed

/--
[ComplexVectorBundleData.curvature_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernClassProperties.lean)
-/
@[path]
lemma ComplexVectorBundleData.curvature_closed
  [AddCommGroup V]
  [Module ℝ V]
  [NormedAddCommGroup EModel]
  [NormedSpace ℝ EModel]
  [TopologicalSpace HModel]
  {I : ModelWithCorners ℝ EModel HModel}
  [TopologicalSpace M]
  [ChartedSpace HModel M]
  [IsManifold I ⊤ M]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {E : M → Type*}
  [TopologicalSpace (Bundle.TotalSpace F E)]
  [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E]
  [VectorBundle ℂ F E]
  {Ω : ℕ → Type*}
  [∀ p, AddCommGroup (Ω p)]
  [∀ p, Module ℝ (Ω p)]
  {d : ∀ {p : ℕ}, Ω p → Ω (p + 1)}
  {d_squared : ∀ {p : ℕ} (α : Ω p), d (d α) = 0}
  {r : ℕ}
  [CommRing totalAlg]
  {intCoh : IsIntegralCohomologyClass Ω d}
  {bundle : ComplexVectorBundleData I M F E Ω d d_squared intCoh r totalAlg} :
-- imply
  d bundle.curvatureRep = 0 := by
-- proof
  rw [← bundle.curvature_eq]
  exact d_squared bundle.connectionForm
/-- Axiomatic form of Proposition 1: on a compact oriented manifold, the top Chern class equals
the Euler class, $c_r(E) = e(E) \in H^{2r}(M, \mathbb{Z})$ — equivalently, $c_r - e$ is exact. -/
end TopChernEuler


-- created on 2026-10-23
