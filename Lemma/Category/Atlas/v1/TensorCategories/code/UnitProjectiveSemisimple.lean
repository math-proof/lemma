import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.v1.Atlas.TensorCategories.code.UnitProjectiveSemisimple
open CategoryTheory MonoidalCategory Limits UnitProjectiveSemisimple


namespace UnitProjectiveSemisimple

/--
[Proposition_1_13_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitProjectiveSemisimple.lean)
-/
@[path]
lemma Proposition_1_13_6
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {P X : C}
  [hP : Projective P]
  [hX : HasRightDual X]
-- given
  (whiskerRight_epi : ∀ {A B : C} (f : A ⟶ B) [Epi f] (Z : C), Epi (f ▷ Z)) :
-- imply
  Projective (P ⊗ X) where factors := by
-- proof
  intro E Y f e he
  let f' : P ⟶ Y ⊗ Xᘁ := (tensorRightHomEquiv P X (Xᘁ) Y) f
  have he' : Epi (e ▷ Xᘁ) := whiskerRight_epi e (Xᘁ)
  obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ Xᘁ)
  use (tensorRightHomEquiv P X (Xᘁ) E).symm g'
  apply (tensorRightHomEquiv P X (Xᘁ) Y).injective
  rw [tensorRightHomEquiv_naturality]
  change (tensorRightHomEquiv P X (Xᘁ) E) ((tensorRightHomEquiv P X (Xᘁ) E).symm g') ≫
    e ▷ Xᘁ = f'
  rwa [Equiv.apply_symm_apply]
section Cor_1_13_7
variable (k : Type*) [Field k]
variable (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
/-- In a multiring category, if every object is projective then the category is
semisimple. -/
end Cor_1_13_7

end UnitProjectiveSemisimple


-- created on 2026-10-23
