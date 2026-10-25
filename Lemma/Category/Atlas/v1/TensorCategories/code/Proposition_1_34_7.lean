import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
open CategoryTheory MonoidalCategory


/--
[Proposition_1_34_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_34_7.lean)
-/
@[path]
lemma Proposition_1_34_7
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear k C]
  [Abelian C]
  [MonoidalCategory C]
  [MonoidalPreadditive C]
  [MonoidalLinear k C]
  {F₁ F₂ : TensorCategories.QuasiFiberFunctor k C}
-- given
  (hHomFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)) :
-- imply
  Nonempty (F₁.F ≅ F₂.F) :=
-- proof
  TensorCategories.prop_1_34_7 k C hHomFiniteDim F₁ F₂


-- created on 2026-10-23
