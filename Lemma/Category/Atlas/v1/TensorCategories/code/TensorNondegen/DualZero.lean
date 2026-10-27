import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.TensorNondegen.DualZero
open CategoryTheory MonoidalCategory Limits


namespace CategoryTheory

/--
[isZero_of_isZero_leftDual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/DualZero.lean)
-/
@[path]
lemma isZero_of_isZero_leftDual
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [MonoidalPreadditive C]
  {X : C}
  [HasLeftDual X]
-- given
  (h : IsZero (ᘁX : C)) :
-- imply
  IsZero X := by
-- proof
  rw [IsZero.iff_id_eq_zero]
  have hid : 𝟙 (ᘁX : C) = 0 := (IsZero.iff_id_eq_zero _).mp h
  have hYX_zero : 𝟙 ((ᘁX : C) ⊗ X) = 0 := by
    rw [← id_whiskerRight (ᘁX : C) X, hid, MonoidalPreadditive.zero_whiskerRight]
  have heta : η_ (ᘁX : C) X = 0 := by
    calc η_ (ᘁX : C) X = η_ (ᘁX : C) X ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = η_ (ᘁX : C) X ≫ 0 := by rw [hYX_zero]
      _ = 0 := comp_zero
  have h_whisker : X ◁ η_ (ᘁX : C) X = 0 := by
    rw [heta, MonoidalPreadditive.whiskerLeft_zero]
  have htri := ExactPairing.coevaluation_evaluation (ᘁX : C) X
  rw [h_whisker, zero_comp] at htri
  have hlambda_inv : (λ_ X).inv = 0 := by
    calc (λ_ X).inv = (ρ_ X).inv ≫ ((ρ_ X).hom ≫ (λ_ X).inv) := by rw [Iso.inv_hom_id_assoc]
      _ = (ρ_ X).inv ≫ 0 := by rw [htri]
      _ = 0 := comp_zero
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := (Iso.inv_hom_id _).symm
    _ = 0 ≫ (λ_ X).hom := by rw [hlambda_inv]
    _ = 0 := zero_comp

end CategoryTheory

namespace CategoryTheory

/--
[isZero_leftDual_of_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/DualZero.lean)
-/
@[path]
lemma isZero_leftDual_of_isZero
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [MonoidalPreadditive C]
  {X : C}
  [HasLeftDual X]
-- given
  (h : IsZero X) :
-- imply
  IsZero (ᘁX : C) := by
-- proof
  rw [IsZero.iff_id_eq_zero]
  have hid : 𝟙 X = 0 := (IsZero.iff_id_eq_zero X).mp h
  have hXY_zero : 𝟙 (X ⊗ (ᘁX : C)) = 0 := by
    rw [← id_whiskerRight X (ᘁX : C), hid, MonoidalPreadditive.zero_whiskerRight]
  have heps : ε_ (ᘁX : C) X = 0 := by
    calc ε_ (ᘁX : C) X = 𝟙 _ ≫ ε_ (ᘁX : C) X := (Category.id_comp _).symm
      _ = 0 ≫ ε_ (ᘁX : C) X := by rw [hXY_zero]
      _ = 0 := zero_comp
  have h_whisker : (ᘁX : C) ◁ ε_ (ᘁX : C) X = 0 := by
    rw [heps, MonoidalPreadditive.whiskerLeft_zero]
  have htri := ExactPairing.evaluation_coevaluation (ᘁX : C) X
  rw [h_whisker, comp_zero, comp_zero] at htri
  have hrho_inv : (ρ_ (ᘁX : C)).inv = 0 := by
    calc (ρ_ (ᘁX : C)).inv
      = (λ_ (ᘁX : C)).inv ≫ ((λ_ (ᘁX : C)).hom ≫ (ρ_ (ᘁX : C)).inv) := by
        rw [Iso.inv_hom_id_assoc]
      _ = (λ_ (ᘁX : C)).inv ≫ 0 := by rw [htri]
      _ = 0 := comp_zero
  calc 𝟙 (ᘁX : C) = (ρ_ (ᘁX : C)).inv ≫ (ρ_ (ᘁX : C)).hom := (Iso.inv_hom_id _).symm
    _ = 0 ≫ (ρ_ (ᘁX : C)).hom := by rw [hrho_inv]
    _ = 0 := zero_comp

end CategoryTheory

/--
[isZero_of_isZero_rightDual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/DualZero.lean)
-/
@[path]
private lemma isZero_of_isZero_rightDual_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [MonoidalPreadditive C]
  {X : C}
  [HasRightDual X]
-- given
  (h : IsZero (Xᘁ)) :
-- imply
  IsZero X := by
-- proof
  apply CategoryTheory.isZero_of_isZero_rightDual h

/--
[isZero_rightDual_of_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/DualZero.lean)
-/
@[path]
private lemma isZero_rightDual_of_isZero_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Preadditive C]
  [MonoidalPreadditive C]
  {X : C}
  [HasRightDual X]
-- given
  (h : IsZero X) :
-- imply
  IsZero (Xᘁ) := by
-- proof
  apply CategoryTheory.isZero_rightDual_of_isZero h


-- created on 2026-10-23
