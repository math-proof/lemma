import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.CoalgebraBialgebra
open Coalgebra CategoryTheory
open scoped TensorProduct
open MonoidalCategory


/--
[unit_endo_comp_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean)
-/
@[path]
lemma unit_endo_comp_eval
  {k : Type u}
  [CommRing k]
  {C : Type v}
  [Category.{w} C]
  [MonoidalCategory C]
  [Preadditive C]
  [Linear k C]
  {F : C ⥤ ModuleCat.{u} k}
  [F.Monoidal]
  [F.Faithful]
  {f g : 𝟙_ (ModuleCat.{u} k) ⟶ 𝟙_ (ModuleCat.{u} k)} :
-- imply
  (f ≫ g).hom (1 : k) = f.hom (1 : k) * g.hom (1 : k) := by
-- proof
  show g.hom (f.hom 1) = f.hom 1 * g.hom 1
  have := g.hom.map_smul (f.hom 1) (1 : k)
  simp only [smul_eq_mul, mul_one] at this
  exact this

/--
[endF_tensor_hom_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean)
-/
@[path]
lemma endF_tensor_hom_tmul
  {X Y : C}
  {η₁ η₂ : End F} :
-- imply
  endF_tensor_hom k C F X Y (η₁ ⊗ₜ[k] η₂) = η₁.app X ⊗ₘ η₂.app Y := by
-- proof
  simp only [endF_tensor_hom, LinearMap.comp_apply, TensorProduct.map_tmul,
    evalAtHom, wrapEnd, LinearMap.coe_mk, AddHom.coe_mk]
  apply ModuleCat.hom_ext; rfl

/--
[endF_counit_one_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean)
-/
@[path]
lemma endF_counit_one_proof
-- imply
  endF_counit_def k C F 1 = 1 := by
-- proof
  show ((Functor.Monoidal.εIso F).hom ≫ (1 : End F).app (𝟙_ C) ≫
    (Functor.Monoidal.εIso F).inv).hom (1 : k) = 1
  rw [show (1 : End F).app (𝟙_ C) = 𝟙 (F.obj (𝟙_ C)) from rfl]
  rw [Category.id_comp, Iso.hom_inv_id]
  rfl

/--
[endF_mul_compr₂_counit_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean)
-/
@[path]
lemma endF_mul_compr₂_counit_proof :
  (LinearMap.mul k (End F)).compr₂ (endF_counit_def k C F) =
    (LinearMap.mul k k).compl₁₂ (endF_counit_def k C F) (endF_counit_def k C F) := by
  ext η ν
  simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', endF_counit_def,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compl₁₂_apply]
  have hmul : (η * ν).app (𝟙_ C) = ν.app (𝟙_ C) ≫ η.app (𝟙_ C) := rfl
  rw [hmul]
  have h_reassoc : (Functor.Monoidal.εIso F).hom ≫
    (ν.app (𝟙_ C) ≫ η.app (𝟙_ C)) ≫ (Functor.Monoidal.εIso F).inv =
    ((Functor.Monoidal.εIso F).hom ≫ ν.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv) ≫
    ((Functor.Monoidal.εIso F).hom ≫ η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv) := by
    simp only [Category.assoc]; congr 1; congr 1; rw [Iso.inv_hom_id_assoc]
  rw [h_reassoc, unit_endo_comp_eval, mul_comm]

/--
[Coalgebra.exists_fg_submodule_comul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean)
-/
@[path]
lemma Coalgebra.exists_fg_submodule_comul_mem
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {c : C} :
-- imply
  ∃ V : Submodule R C, V.FG ∧ c ∈ V ∧ Coalgebra.comul c ∈ Submodule.map₂ (TensorProduct.mk R C C) ⊤ V := by
-- proof
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := R) (Coalgebra.comul c)
  let V := Submodule.span R (Finset.image Prod.snd S : Set C)
  refine ⟨V, ?_, ?_, ?_⟩
  ·
    exact Submodule.fg_span (Finset.image Prod.snd S).finite_toSet
  ·
    have hcounit := Coalgebra.rTensor_counit_comul (R := R) c
    rw [hS] at hcounit
    simp only [map_sum, LinearMap.rTensor_tmul] at hcounit
    have hc : c = ∑ p ∈ S, Coalgebra.counit (R := R) p.1 • p.2 := by
      have := congr_arg (TensorProduct.lid R C) hcounit
      simp only [map_sum, TensorProduct.lid_tmul, one_smul] at this
      exact this.symm
    rw [hc]
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hp))
  ·
    rw [hS]
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.apply_mem_map₂ _ Submodule.mem_top
      (Submodule.subset_span (Finset.mem_image_of_mem _ hp))

/--
[endF_mul_compr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean)
-/
@[path]
private lemma endF_mul_compr_eq :
-- imply
  (LinearMap.mul k (End F)).compr₂ (endF_counit_def k C F) = (LinearMap.mul k k).compl₁₂ (endF_counit_def k C F) (endF_counit_def k C F) := by
-- proof
  apply endF_mul_compr


-- created on 2026-10-23
