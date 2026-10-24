import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.FPdimProps
open CategoryTheory
open CategoryTheory MonoidalCategory Limits


namespace CategoryTheory

/--
[hom_tensor_right_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimProps.lean)
-/
@[path]
lemma hom_tensor_right_finrank_eq
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear k C]
  [MonoidalCategory C]
  [MonoidalPreadditive C]
  [MonoidalLinear k C]
  [RigidCategory C]
  {X Z Y : C} :
-- imply
  Module.finrank k (X ⊗ Z ⟶ Y) = Module.finrank k (X ⟶ Y ⊗ Zᘁ) :=
-- proof
  LinearEquiv.finrank_eq (tensorRightHomLinearEquiv k X Z Y)

end CategoryTheory

namespace CategoryTheory

/--
[hom_tensor_left_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimProps.lean)
-/
@[path]
lemma hom_tensor_left_finrank_eq
  {k : Type w}
  [Field k]
  {Z P Y : C} :
-- imply
  Module.finrank k (Z ⊗ P ⟶ Y) = Module.finrank k (P ⟶ (ᘁZ) ⊗ Y) :=
-- proof
  LinearEquiv.finrank_eq (tensorLeftHomLinearEquiv Z P Y)

end CategoryTheory


-- created on 2026-10-23
