import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
open CategoryTheory MonoidalCategory


/--
[zigzag_inv_eval_coeval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InvertibleObjects.lean)
-/
@[path]
private lemma zigzag_inv_eval_coeval_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {X : C}
  [HasRightDual X]
  [IsIso (ε_ X (Xᘁ))]
  [IsIso (η_ X (Xᘁ))] :
-- imply
  (inv (ε_ X Xᘁ) ▷ Xᘁ) ≫ (α_ Xᘁ X Xᘁ).hom ≫ (Xᘁ ◁ inv (η_ X Xᘁ)) = (λ_ Xᘁ).hom ≫ (ρ_ Xᘁ).inv := by
-- proof
  apply CategoryTheory.zigzag_inv_eval_coeval X

/--
[zigzag_inv_coeval_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InvertibleObjects.lean)
-/
@[path]
private lemma zigzag_inv_coeval_eval_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {X : C}
  [HasRightDual X]
  [IsIso (ε_ X (Xᘁ))]
  [IsIso (η_ X (Xᘁ))] :
-- imply
  (X ◁ inv (ε_ X Xᘁ)) ≫ (α_ X Xᘁ X).inv ≫ (inv (η_ X Xᘁ) ▷ X) = (ρ_ X).hom ≫ (λ_ X).inv := by
-- proof
  apply CategoryTheory.zigzag_inv_coeval_eval X


-- created on 2026-10-23
