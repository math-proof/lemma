import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
open Category MonoidalCategory LeftModCat


namespace CategoryTheory

/--
[corollary_2_7_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_2_7_2.lean)
-/
@[path]
lemma corollary_2_7_2
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [ExactModuleCategory C M]
  [Field k]
  [Abelian C]
  [Linear k C]
  [Abelian M]
  [Linear k M]
  [hC : IsFiniteAbelianCategory k C]
-- given
  (hFinSimples : ∃ (n : ℕ) (S : Fin n → M), (∀ i, Simple (S i)) ∧ (∀ (X : M), Simple X → ∃ i, Nonempty (X ≅ S i))) :
-- imply
  IsFiniteAbelianCategory k M :=
-- proof
  ExactModuleCategory.isFiniteAbelianCategory_of_exact (k := k) (C := C) hFinSimples

end CategoryTheory


-- created on 2026-10-23
