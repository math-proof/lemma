import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.Theorem_2_11_2.Part2
open CategoryTheory
open Category MonoidalCategory


namespace CategoryTheory

/--
[thm_2_11_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_2_11_2.lean)
-/
@[path]
lemma thm_2_11_2
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
-- given
  (hom : InternalHomData₂ C M)
  (hExact : InternalHomRightExact₂ hom)
  (hGen : InternalHomGeneration₂ hom) :
-- imply
  Nonempty (M ≌ ModC₂ hom.endAlg) :=
-- proof
  ⟨theorem_2_11_2_equiv hom hExact hGen⟩

end CategoryTheory


-- created on 2026-10-23
