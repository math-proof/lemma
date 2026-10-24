import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.TannakaBialgebra
open CategoryTheory TensorCategories


/--
[tannaka_reconstruction_bialgebra_1_34_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaBialgebra.lean)
-/
@[path]
private lemma tannaka_reconstruction_bialgebra_1_34_8_eq
  {k : Type w}
  [Field k]
  {C : Type (w+1)}
  [Category.{w} C]
  [MonoidalCategory C]
  [Abelian C]
  [Linear k C]
  {QF : QuasiFiberFunctor k C} :
-- imply
  ∃ (data : QuasiBialgebraReconstructionData k C), Nonempty (MonoidalEquiv_134 C data.RepH) := by
-- proof
  apply tannaka_reconstruction_bialgebra_1_34_8 k C QF


-- created on 2026-10-23
