import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.MonoidalUnitProperties
open CategoryTheory MonoidalCategory Category TensorCategories


namespace TensorCategories

/--
[triangle_diagram](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma triangle_diagram
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y : C} :
-- imply
  (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y :=
-- proof
  MonoidalCategory.triangle X Y

end TensorCategories

namespace TensorCategories

/--
[leftUnitor_unit_eq_rightUnitor_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma leftUnitor_unit_eq_rightUnitor_unit
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
-- proof
  monoidal_coherence

end TensorCategories

namespace TensorCategories

/--
[leftUnitor_unit_eq_rightUnitor_unit_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma leftUnitor_unit_eq_rightUnitor_unit_inv
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by
-- proof
  monoidal_coherence

end TensorCategories

namespace TensorCategories

/--
[prop_1_2_2_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma prop_1_2_2_left
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y : C} :
-- imply
  (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom = (λ_ X).hom ▷ Y := by
-- proof
  simp

end TensorCategories

namespace TensorCategories

/--
[prop_1_2_2_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma prop_1_2_2_right
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y : C} :
-- imply
  (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ X ◁ (ρ_ Y).hom := by
-- proof
  simp

end TensorCategories

namespace TensorCategories

/--
[Proposition_1_2_2_leftUnitor_unit_eq_rightUnitor_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma Proposition_1_2_2_leftUnitor_unit_eq_rightUnitor_unit
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
-- proof
  unitors_equal

end TensorCategories

namespace TensorCategories

/--
[prop_1_2_3_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma prop_1_2_3_left
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X : C} :
-- imply
  (λ_ (𝟙_ C ⊗ X)).hom = (𝟙_ C) ◁ (λ_ X).hom := by
-- proof
  rw [leftUnitor_tensor_hom, leftUnitor_unit_eq_rightUnitor_unit,
    ← MonoidalCategory.triangle]
  simp

end TensorCategories

namespace TensorCategories

/--
[prop_1_2_3_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma prop_1_2_3_right
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X : C} :
-- imply
  (ρ_ (X ⊗ 𝟙_ C)).hom = (ρ_ X).hom ▷ (𝟙_ C) := by
-- proof
  rw [rightUnitor_tensor_hom, ← leftUnitor_unit_eq_rightUnitor_unit]
  simp

end TensorCategories

namespace TensorCategories

/--
[Proposition_1_2_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma Proposition_1_2_3
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X : C} :
-- imply
  (λ_ (𝟙_ C ⊗ X)).hom = (𝟙_ C) ◁ (λ_ X).hom ∧ (ρ_ (X ⊗ 𝟙_ C)).hom = (ρ_ X).hom ▷ (𝟙_ C) :=
-- proof
  ⟨prop_1_2_3_left X, prop_1_2_3_right X⟩

end TensorCategories

namespace TensorCategories

/--
[prop_1_2_4_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma prop_1_2_4_existence
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {U : C}
-- given
  (hU : IsUnitObject U) :
-- imply
  Nonempty (𝟙_ C ≅ U) :=
-- proof
  ⟨unit_object_iso_of_isUnit U hU⟩

end TensorCategories

namespace TensorCategories

/--
[unit_iso_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma unit_iso_unique
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  (λ_ (𝟙_ C)) = (ρ_ (𝟙_ C)) := by
-- proof
  ext
  exact leftUnitor_unit_eq_rightUnitor_unit

end TensorCategories

namespace TensorCategories

/--
[unit_unique_self_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma unit_unique_self_iso
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  (λ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
-- proof
  rw [leftUnitor_unit_eq_rightUnitor_unit_inv]
  simp

end TensorCategories

namespace TensorCategories

/--
[tensorHom_id_right_unit_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma tensorHom_id_right_unit_comm
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {c : 𝟙_ C ⟶ 𝟙_ C} :
-- imply
  (c ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ c := by
-- proof
  simp [MonoidalCategory.tensorHom_def]

end TensorCategories

namespace TensorCategories

/--
[unit_endo_compat_is_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma unit_endo_compat_is_id
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
  have h_nat : (b ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ b :=
    tensorHom_id_right_unit_comm b
  have h_eq : b ⊗ₘ b = b ⊗ₘ 𝟙 (𝟙_ C) :=
    (cancel_mono (ρ_ (𝟙_ C)).hom).mp (hb.trans h_nat.symm)
  have h_whisker : (𝟙_ C) ◁ b = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
    have h1 : b ⊗ₘ b = b ▷ (𝟙_ C) ≫ (𝟙_ C) ◁ b := MonoidalCategory.tensorHom_def b b
    have h2 : b ⊗ₘ 𝟙 (𝟙_ C) = b ▷ (𝟙_ C) := by
      simp [MonoidalCategory.tensorHom_def]
    rw [h1, h2] at h_eq
    rwa [← cancel_epi (b ▷ (𝟙_ C)), comp_id]
  have h_lnat := leftUnitor_naturality (C := C) b
  rw [h_whisker, id_comp] at h_lnat
  rwa [← cancel_epi (λ_ (𝟙_ C)).hom, comp_id]

end TensorCategories

namespace TensorCategories

/--
[unit_iso_compatible_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma unit_iso_compatible_unique
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {U : C}
  {f g : 𝟙_ C ≅ U}
-- given
  (hU : IsUnitObject U)
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
  apply unit_endo_compat_is_id
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  have cancel_g : r'_U ≫ g.inv = (g.inv ⊗ₘ g.inv) ≫ (ρ_ (𝟙_ C)).hom := by
    rw [← cancel_epi (g.hom ⊗ₘ g.hom)]
    rw [← assoc, hg, assoc, Iso.hom_inv_id, comp_id]
    rw [← assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hf_ginv : (f.hom ⊗ₘ f.hom) ≫ r'_U ≫ g.inv = (ρ_ (𝟙_ C)).hom ≫ f.hom ≫ g.inv := by
    rw [← assoc, hf, assoc]
  rwa [assoc, ← cancel_g]

end TensorCategories

namespace TensorCategories

/--
[Proposition_1_2_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma Proposition_1_2_4
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {U : C}
-- given
  (hU : IsUnitObject U) :
-- imply
  (∃ η : 𝟙_ C ≅ U, True) ∧ (∀ (f g : 𝟙_ C ≅ U), (f.hom ⊗ₘ f.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ f.hom → (g.hom ⊗ₘ g.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ g.hom → f = g) :=
-- proof
  ⟨⟨unit_object_iso_of_isUnit U hU, trivial⟩,
    fun f g hf hg => unit_iso_compatible_unique U hU f g hf hg⟩

end TensorCategories

namespace TensorCategories

/--
[tensorHom_via_rightUnitor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma tensorHom_via_rightUnitor_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {f g : 𝟙_ C ⟶ 𝟙_ C} :
-- imply
  (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ (𝟙_ C)).hom = f ≫ g := by
-- proof
  rw [rightUnitor_inv_comp_tensorHom_assoc]
  rw [← leftUnitor_unit_eq_rightUnitor_unit, leftUnitor_naturality,
    leftUnitor_unit_eq_rightUnitor_unit]
  simp

end TensorCategories

namespace TensorCategories

/--
[tensorHom_via_rightUnitor_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma tensorHom_via_rightUnitor_eq'
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {f g : 𝟙_ C ⟶ 𝟙_ C} :
-- imply
  (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ (𝟙_ C)).hom = g ≫ f := by
-- proof
  rw [← leftUnitor_unit_eq_rightUnitor_unit_inv,
    leftUnitor_inv_comp_tensorHom_assoc]
  rw [rightUnitor_naturality]
  simp [leftUnitor_unit_eq_rightUnitor_unit_inv]

end TensorCategories

namespace TensorCategories

/--
[endomorphism_unit_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma endomorphism_unit_comm
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {f g : 𝟙_ C ⟶ 𝟙_ C} :
-- imply
  f ≫ g = g ≫ f := by
-- proof
  rw [← tensorHom_via_rightUnitor_eq, tensorHom_via_rightUnitor_eq']

end TensorCategories

namespace TensorCategories

/--
[endomorphism_unit_mul_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma endomorphism_unit_mul_comm
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {f g : End (𝟙_ C)} :
-- imply
  f * g = g * f := by
-- proof
  show g ≫ f = f ≫ g
  exact (endomorphism_unit_comm f g).symm

end TensorCategories

namespace TensorCategories

/--
[Proposition_1_2_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean)
-/
@[path]
lemma Proposition_1_2_7
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {f g : 𝟙_ C ⟶ 𝟙_ C} :
-- imply
  f ≫ g = g ≫ f :=
-- proof
  endomorphism_unit_comm f g

end TensorCategories


-- created on 2026-10-23
