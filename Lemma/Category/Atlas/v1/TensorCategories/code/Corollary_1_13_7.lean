import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.v1.Atlas.TensorCategories.code.Corollary_1_13_7
open CategoryTheory MonoidalCategory Limits


/--
[proposition_1_13_6_projective_tensor_right_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_13_7.lean)
-/
@[path]
lemma proposition_1_13_6_projective_tensor_right_dual
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {P X : C}
  [Projective P]
  [HasRightDual X]
-- given
  (whiskerRight_epi : ∀ {A B : C} (f : A ⟶ B) [Epi f] (Z : C), Epi (f ▷ Z)) :
-- imply
  Projective (P ⊗ X) where factors := by
-- proof
  intro E Y f e he
  let f' : P ⟶ Y ⊗ Xᘁ := (tensorRightHomEquiv P X (Xᘁ) Y) f
  have _he' : Epi (e ▷ Xᘁ) := whiskerRight_epi e (Xᘁ)
  obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ Xᘁ)
  use (tensorRightHomEquiv P X (Xᘁ) E).symm g'
  apply (tensorRightHomEquiv P X (Xᘁ) Y).injective
  rw [tensorRightHomEquiv_naturality]
  change (tensorRightHomEquiv P X (Xᘁ) E) ((tensorRightHomEquiv P X (Xᘁ) E).symm g') ≫
    e ▷ Xᘁ = f'
  rwa [Equiv.apply_symm_apply]
variable (k : Type*) [Field k]
variable (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
/-- In a multiring category, if every object is projective then `C` is semisimple. -/


-- created on 2026-10-23
