import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part4
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits TensorCategories


namespace TensorCategories

/--
[Theorem_1_15_1_endUnit_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
lemma Theorem_1_15_1_endUnit_semisimple
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [inst_ab : Abelian C]
  [MonoidalBiexact C]
  [IsArtinianRing (End (𝟙_ C))] :
-- imply
  IsSemisimpleRing (End (𝟙_ C)) :=
-- proof
  endUnit_isSemisimpleRing

end TensorCategories

/--
[endUnit_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma endUnit_comm_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {f g : 𝟙_ C ⟶ 𝟙_ C} :
-- imply
  f ≫ g = g ≫ f := by
-- proof
  apply TensorCategories.endUnit_comm f g

/--
[tensorHom_sq_of_sq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma tensorHom_sq_of_sq_zero_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  {f : 𝟙_ C ⟶ 𝟙_ C}
-- given
  (hf : f ≫ f = 0) :
-- imply
  f ⊗ₘ f = 0 := by
-- proof
  apply TensorCategories.tensorHom_sq_of_sq_zero f hf

/--
[isZero_of_tensorSelf_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma isZero_of_tensorSelf_isZero_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  {X : C}
-- given
  (h : IsZero (X ⊗ X)) :
-- imply
  IsZero X := by
-- proof
  apply TensorCategories.isZero_of_tensorSelf_isZero X h

/--
[tensorHom_mono_of_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma tensorHom_mono_of_mono_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [MonoidalBiexact C]
  {X₁ Y₁ X₂ Y₂ : C}
  {f : X₁ ⟶ Y₁}
  {g : X₂ ⟶ Y₂}
  [Mono f]
  [Mono g] :
-- imply
  Mono (f ⊗ₘ g) := by
-- proof
  apply TensorCategories.tensorHom_mono_of_mono f g

/--
[tensorHom_epi_of_epi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma tensorHom_epi_of_epi_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [MonoidalBiexact C]
  {X₁ Y₁ X₂ Y₂ : C}
  {f : X₁ ⟶ Y₁}
  {g : X₂ ⟶ Y₂}
  [Epi f]
  [Epi g] :
-- imply
  Epi (f ⊗ₘ g) := by
-- proof
  apply TensorCategories.tensorHom_epi_of_epi f g

/--
[isZero_of_epi_comp_mono_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma isZero_of_epi_comp_mono_eq_zero_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {A B D : C}
  {e : A ⟶ B}
  {m : B ⟶ D}
  [Epi e]
  [Mono m]
-- given
  (h : e ≫ m = 0) :
-- imply
  IsZero B := by
-- proof
  apply TensorCategories.isZero_of_epi_comp_mono_eq_zero e m h

/--
[tensorImage_zero_of_tensorHom_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma tensorImage_zero_of_tensorHom_zero_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [MonoidalBiexact C]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [MonoidalBiexact C]
  {f : 𝟙_ C ⟶ 𝟙_ C}
-- given
  (hf : f ⊗ₘ f = 0) :
-- imply
  f = 0 := by
-- proof
  apply TensorCategories.tensorImage_zero_of_tensorHom_zero f hf

/--
[isReduced_of_sq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma isReduced_of_sq_zero_eq
  [MonoidWithZero R]
-- given
  (h : ∀ x : R, x * x = 0 → x = 0) :
-- imply
  IsReduced R := by
-- proof
  apply TensorCategories.isReduced_of_sq_zero h

/--
[endUnit_isReduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma endUnit_isReduced_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [MonoidalBiexact C] :
-- imply
  IsReduced (End (𝟙_ C)) := by
-- proof
  apply TensorCategories.endUnit_isReduced

/--
[endUnit_isSemisimpleRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean)
-/
@[path]
private lemma endUnit_isSemisimpleRing_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [inst_ab : Abelian C]
  [MonoidalBiexact C]
  [IsArtinianRing (End (𝟙_ C))] :
-- imply
  IsSemisimpleRing (End (𝟙_ C)) := by
-- proof
  apply TensorCategories.endUnit_isSemisimpleRing


-- created on 2026-10-23
