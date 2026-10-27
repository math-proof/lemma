import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.Proposition_1_2_4
open CategoryTheory MonoidalCategory


namespace CategoryTheory

/--
[unit_endo_compat_is_id'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_2_4.lean)
-/
@[path]
lemma unit_endo_compat_is_id'
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {b : 𝟙_ C ⟶ 𝟙_ C}
  [IsIso b]
-- given
  (hb : (b ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ b) :
-- imply
  b = 𝟙 (𝟙_ C) := by
-- proof
  have nat_b : b ▷ 𝟙_ C ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ b :=
    rightUnitor_naturality b
  have h_tensor_eq_whisk : b ⊗ₘ b = b ▷ 𝟙_ C := by
    have : (b ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom = (b ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom := by
      rw [hb, nat_b]
    exact (cancel_mono (ρ_ (𝟙_ C)).hom).mp this
  have h_def : b ⊗ₘ b = b ▷ 𝟙_ C ≫ 𝟙_ C ◁ b :=
    MonoidalCategory.tensorHom_def b b
  have h_comp : b ▷ 𝟙_ C ≫ 𝟙_ C ◁ b = b ▷ 𝟙_ C := by
    rw [← h_def, h_tensor_eq_whisk]
  have h_whisk_id : 𝟙_ C ◁ b = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
    rw [← cancel_epi (b ▷ 𝟙_ C)]
    rw [h_comp, Category.comp_id]
  have h_lambda : (λ_ (𝟙_ C)).hom ≫ b = (λ_ (𝟙_ C)).hom := by
    rw [← leftUnitor_naturality b, h_whisk_id, Category.id_comp]
  exact (cancel_epi (λ_ (𝟙_ C)).hom).mp (by rw [h_lambda, Category.comp_id])

end CategoryTheory

namespace CategoryTheory

/--
[unit_iso_compatible_unique'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_2_4.lean)
-/
@[path]
lemma unit_iso_compatible_unique'
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {U : C}
  {f g : 𝟙_ C ≅ U}
-- given
  (hU : IsUnitObject' U)
  (hf : (f.hom ⊗ₘ f.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ f.hom)
  (hg : (g.hom ⊗ₘ g.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ g.hom) :
-- imply
  f = g := by
-- proof
  let r'_U : U ⊗ U ⟶ U := hU.rightUnitor'.hom.app U
  change (f.hom ⊗ₘ f.hom) ≫ r'_U = (ρ_ (𝟙_ C)).hom ≫ f.hom at hf
  change (g.hom ⊗ₘ g.hom) ≫ r'_U = (ρ_ (𝟙_ C)).hom ≫ g.hom at hg
  ext
  suffices h : f.hom ≫ g.inv = 𝟙 (𝟙_ C) by
    have := congr_arg (· ≫ g.hom) h
    simp at this
    exact this
  apply unit_endo_compat_is_id'
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  have cancel_g : r'_U ≫ g.inv = (g.inv ⊗ₘ g.inv) ≫ (ρ_ (𝟙_ C)).hom := by
    rw [← cancel_epi (g.hom ⊗ₘ g.hom)]
    rw [← Category.assoc, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hf_ginv : (f.hom ⊗ₘ f.hom) ≫ r'_U ≫ g.inv = (ρ_ (𝟙_ C)).hom ≫ f.hom ≫ g.inv := by
    rw [← Category.assoc, hf, Category.assoc]
  rwa [Category.assoc, ← cancel_g]

end CategoryTheory

namespace CategoryTheory

/--
[Proposition_1_2_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_2_4.lean)
-/
@[path]
lemma Proposition_1_2_4
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {U : C}
-- given
  (hU : IsUnitObject' U) :
-- imply
  Nonempty (𝟙_ C ≅ U) ∧ (∀ (f g : 𝟙_ C ≅ U), (f.hom ⊗ₘ f.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ f.hom → (g.hom ⊗ₘ g.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ g.hom → f = g) :=
-- proof
  ⟨⟨unit_object_iso' U hU⟩,
    fun f g hf hg => unit_iso_compatible_unique' U hU f g hf hg⟩

end CategoryTheory


-- created on 2026-10-23
