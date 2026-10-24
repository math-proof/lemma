import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.PivotalSpherical
open CategoryTheory MonoidalCategory Category Limits TensorCategories


namespace TensorCategories

/--
[leftTrace_eq_rightTrace_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean)
-/
@[path]
lemma leftTrace_eq_rightTrace_dual
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {V : C}
  {a : V ⟶ (Vᘁ)ᘁ} :
-- imply
  leftQuantumTrace C a = η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ) := by
-- proof
  unfold leftQuantumTrace
  have h := (CategoryTheory.coevaluation_comp_rightAdjointMate a).symm
  calc η_ V Vᘁ ≫ a ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ
    = (η_ V Vᘁ ≫ a ▷ Vᘁ) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [assoc]
    _ = (η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ)) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [h]
    _ = η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [assoc]

end TensorCategories

namespace TensorCategories

/--
[leftTrace_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean)
-/
@[path]
lemma leftTrace_comp_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {V : C}
  {a : V ⟶ (Vᘁ)ᘁ}
  {c : V ⟶ V} :
-- imply
  leftQuantumTrace C (c ≫ a) = leftQuantumTrace C (a ≫ (cᘁ)ᘁ) := by
-- proof
  unfold leftQuantumTrace
  simp only [comp_whiskerRight, assoc]
  have step1 : η_ V Vᘁ ≫ c ▷ Vᘁ = η_ V Vᘁ ≫ V ◁ (cᘁ : Vᘁ ⟶ Vᘁ) :=
    (CategoryTheory.coevaluation_comp_rightAdjointMate c).symm
  have step2 : (V ◁ (cᘁ : Vᘁ ⟶ Vᘁ)) ≫ (a ▷ Vᘁ) =
    (a ▷ Vᘁ) ≫ ((Vᘁ)ᘁ ◁ (cᘁ : Vᘁ ⟶ Vᘁ)) :=
    CategoryTheory.MonoidalCategory.whisker_exchange a (cᘁ : Vᘁ ⟶ Vᘁ)
  have step3 : ((Vᘁ)ᘁ ◁ (cᘁ : Vᘁ ⟶ Vᘁ)) ≫ ε_ Vᘁ ((Vᘁ)ᘁ) =
    ((cᘁ)ᘁ ▷ Vᘁ) ≫ ε_ Vᘁ ((Vᘁ)ᘁ) :=
    (CategoryTheory.rightAdjointMate_comp_evaluation (cᘁ : Vᘁ ⟶ Vᘁ)).symm
  calc η_ V Vᘁ ≫ c ▷ Vᘁ ≫ a ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ
    = (η_ V Vᘁ ≫ c ▷ Vᘁ) ≫ a ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [assoc]
    _ = (η_ V Vᘁ ≫ V ◁ cᘁ) ≫ a ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [step1]
    _ = η_ V Vᘁ ≫ (V ◁ cᘁ ≫ a ▷ Vᘁ) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by simp only [assoc]
    _ = η_ V Vᘁ ≫ (a ▷ Vᘁ ≫ (Vᘁ)ᘁ ◁ cᘁ) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [step2]
    _ = η_ V Vᘁ ≫ a ▷ Vᘁ ≫ ((Vᘁ)ᘁ ◁ cᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ) := by simp only [assoc]
    _ = η_ V Vᘁ ≫ a ▷ Vᘁ ≫ ((cᘁ)ᘁ ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ) := by rw [step3]
    _ = η_ V Vᘁ ≫ a ▷ Vᘁ ≫ (cᘁ)ᘁ ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rfl

end TensorCategories

namespace TensorCategories

/--
[rightTrace_comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean)
-/
@[path]
lemma rightTrace_comp_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {V : C}
  {a : V ⟶ ᘁ(ᘁV)}
  {c : V ⟶ V} :
-- imply
  rightQuantumTrace C (c ≫ a) = rightQuantumTrace C (a ≫ leftAdjointMate (leftAdjointMate c)) := by
-- proof
  unfold rightQuantumTrace
  simp only [MonoidalCategory.whiskerLeft_comp, assoc]
  have step1 : η_ (ᘁV) V ≫ ((ᘁV : C) ◁ c) =
    η_ (ᘁV) V ≫ (leftAdjointMate c) ▷ V :=
    (CategoryTheory.coevaluation_comp_leftAdjointMate c).symm
  have step2 : ((leftAdjointMate c) ▷ V) ≫ ((ᘁV : C) ◁ a) =
    ((ᘁV : C) ◁ a) ≫ ((leftAdjointMate c) ▷ (ᘁ(ᘁV) : C)) :=
    (CategoryTheory.MonoidalCategory.whisker_exchange (leftAdjointMate c) a).symm
  have step3 : ((leftAdjointMate c) ▷ (ᘁ(ᘁV) : C)) ≫ ε_ (ᘁ(ᘁV)) (ᘁV) =
    ((ᘁV : C) ◁ leftAdjointMate (leftAdjointMate c)) ≫ ε_ (ᘁ(ᘁV)) (ᘁV) :=
    (CategoryTheory.leftAdjointMate_comp_evaluation (leftAdjointMate c)).symm
  rw [show η_ (ᘁV) V ≫ (ᘁV : C) ◁ c ≫ (ᘁV : C) ◁ a ≫ ε_ (ᘁ(ᘁV)) (ᘁV)
    = (η_ (ᘁV) V ≫ (ᘁV : C) ◁ c) ≫ (ᘁV : C) ◁ a ≫ ε_ (ᘁ(ᘁV)) (ᘁV) from by rw [assoc]]
  rw [step1]
  rw [show (η_ (ᘁV) V ≫ (leftAdjointMate c) ▷ V) ≫ (ᘁV : C) ◁ a ≫ ε_ (ᘁ(ᘁV)) (ᘁV)
    = η_ (ᘁV) V ≫ ((leftAdjointMate c) ▷ V ≫ (ᘁV : C) ◁ a) ≫ ε_ (ᘁ(ᘁV)) (ᘁV) from
    by simp only [assoc]]
  rw [step2]
  rw [show η_ (ᘁV) V ≫ ((ᘁV : C) ◁ a ≫ (leftAdjointMate c) ▷ (ᘁ(ᘁV) : C)) ≫
    ε_ (ᘁ(ᘁV)) (ᘁV)
    = η_ (ᘁV) V ≫ (ᘁV : C) ◁ a ≫
      ((leftAdjointMate c) ▷ (ᘁ(ᘁV) : C) ≫ ε_ (ᘁ(ᘁV)) (ᘁV)) from by simp only [assoc]]
  rw [step3]

end TensorCategories

namespace TensorCategories

/--
[pivotalTrace_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean)
-/
@[path]
lemma pivotalTrace_id
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  [PivotalCategory C]
  {V : C} :
-- imply
  pivotalTrace C (𝟙 V) = pivotalDimension C V := by
-- proof
  unfold pivotalTrace pivotalDimension
  simp

end TensorCategories

namespace TensorCategories

/--
[pivotalDimension_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean)
-/
@[path]
lemma pivotalDimension_unit
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  [PivotalCategory C] :
-- imply
  pivotalDimension C (𝟙_ C) = 𝟙 (𝟙_ C) :=
-- proof
  PivotalCategory.dimUnit (C := C)

end TensorCategories


-- created on 2026-10-23
