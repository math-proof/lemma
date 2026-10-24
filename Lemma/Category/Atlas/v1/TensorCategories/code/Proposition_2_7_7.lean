import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
open CategoryTheory Category MonoidalCategory LeftModCat


namespace CategoryTheory.ExactModuleCategory

/--
[proposition_2_7_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_2_7_7.lean)
-/
@[path]
lemma proposition_2_7_7
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Abelian M]
  [EnoughProjectives M]
  {I : Type*}
  {repr : I → M}
-- given
  (repr_simple : ∀ i, Simple (repr i))
  (classification : ∀ (X : M), Simple X → ∃! i, IrrRelated C M (repr i) X) :
-- imply
  ((∀ (N : M), ∃ i, AllSimpleSubquotientsInClass' C (repr i) N) ∧ (∀ (i : I) (N : M) (L : C), AllSimpleSubquotientsInClass' C (repr i) N → AllSimpleSubquotientsInClass' C (repr i) (L ⊗ᵐ N))) ∧ (∀ (i : I) (P : C) (_ : Projective P) (N : M), AllSimpleSubquotientsInClass' C (repr i) N → AllSimpleSubquotientsInClass' C (repr i) (P ⊗ᵐ N) ∧ Projective (P ⊗ᵐ N)) :=
-- proof
  Proposition_2_7_7 I repr repr_simple classification

end CategoryTheory.ExactModuleCategory


-- created on 2026-10-23
