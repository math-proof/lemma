import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TensorCategories.code.Theorem_1_53_1.Part2
open CategoryTheory MonoidalCategory


/--
[det_eq_zero_of_mulVec_eq_zero_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean)
-/
@[path]
lemma det_eq_zero_of_mulVec_eq_zero_of_ne_zero
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {M : Matrix ι ι k}
  {d : ι → k}
-- given
  (hd : d ≠ 0)
  (hMd : M.mulVec d = 0) :
-- imply
  M.det = 0 := by
-- proof
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨d, hd, hMd⟩

/--
[cartan_matrix_degenerate_of_dim_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean)
-/
@[path]
lemma cartan_matrix_degenerate_of_dim_vanishes
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {C_mat : ι → ι → ℕ}
  {d : ι → k}
-- given
  (hd_ne : d ≠ 0)
  (hd_kernel : ∀ i : ι, ∑ j : ι, (C_mat i j : k) * d j = 0) :
-- imply
  (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0 := by
-- proof
  apply det_eq_zero_of_mulVec_eq_zero_of_ne_zero _ d hd_ne
  ext i
  simp only [Matrix.mulVec, dotProduct, cartanMatrixOverField, Matrix.of_apply, Pi.zero_apply]
  exact hd_kernel i
section PivotalDimensionTheorem
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/--
[dim_proj_zero_of_not_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean)
-/
@[path]
lemma dim_proj_zero_of_not_semisimple
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {u : PivotalStructureData C}
  {φ : (𝟙_ C ⟶ 𝟙_ C) → k}
  {P : C}
  [Projective P]
-- given
  (h_retract : ∀ (P : C) [Projective P], φ (pivotalDim C u P) ≠ 0 → Projective (𝟙_ C))
  (hns : ¬ Projective (𝟙_ C)) :
-- imply
  φ (pivotalDim C u P) = 0 := by
-- proof
  by_contra h
  exact hns (h_retract P h)

/--
[dim_vec_ne_zero_of_component_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean)
-/
@[path]
lemma dim_vec_ne_zero_of_component_ne_zero
  [Field k]
  {d : ι → k}
  {i₀ : ι}
-- given
  (hi₀ : d i₀ ≠ 0) :
-- imply
  d ≠ 0 := by
-- proof
  intro h
  exact hi₀ (congr_fun h i₀)

/--
[thm_1_53_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean)
-/
@[path]
lemma thm_1_53_1
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {u : PivotalStructureData C}
  {ftc : FiniteTensorCategoryData C k ι u}
-- given
  (hns : ¬ Projective (𝟙_ C)) :
-- imply
  (cartanMatrixOverField ftc.cartanEntry : Matrix ι ι k).det = 0 := by
-- proof
  let d : ι → k := fun j => ftc.φ (pivotalDim C u (ftc.simpleObj j))
  have hdP : ∀ i, ftc.φ (pivotalDim C u (ftc.projCover i)) = 0 := by
    intro i
    exact @dim_proj_zero_of_not_semisimple k _ C _ _ _ u ftc.φ
      ftc.retract_of_projective hns (ftc.projCover i) (ftc.projCover_projective i)
  have hkernel : ∀ i, ∑ j : ι, (ftc.cartanEntry i j : k) * d j = 0 := by
    intro i
    rw [ftc.additive_on_composition_series i]
    exact hdP i
  have hdi₀ : d ftc.unitIndex ≠ 0 := by
    intro h
    apply ftc.dim_unit_ne_zero
    rwa [← ftc.dim_iso_invariant (ftc.simpleObj ftc.unitIndex) (𝟙_ C) ftc.unitIso]
  exact cartan_matrix_degenerate_of_dim_vanishes ftc.cartanEntry d
    (dim_vec_ne_zero_of_component_ne_zero d ftc.unitIndex hdi₀) hkernel

/--
[Theorem_1_53_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean)
-/
@[path]
lemma Theorem_1_53_1
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {u : PivotalStructureData C}
  {ftc : FiniteTensorCategoryData C k ι u}
-- given
  (hns : ¬ Projective (𝟙_ C)) :
-- imply
  (cartanMatrixOverField ftc.cartanEntry : Matrix ι ι k).det = 0 :=
-- proof
  thm_1_53_1 u hns ftc


-- created on 2026-10-23
