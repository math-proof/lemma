import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorNondegen.ZeroTensorZero
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits ZeroObject TensorNondegen


/--
[isZero_of_tensorSelf_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/ZeroTensorZero.lean)
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
  apply TensorNondegen.isZero_of_tensorSelf_isZero X h


-- created on 2026-10-23
