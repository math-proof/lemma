module

public import Mathlib
public import Structure.v1.Atlas.TensorCategories.code.TannakaBialgebra

public section

open CategoryTheory TensorCategories


/--
[tannaka_reconstruction_bialgebra_1_34_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaBialgebra.lean)
-/
public theorem tannaka_reconstruction_bialgebra_1_34_8_eq
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
