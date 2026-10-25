import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.MfStarAlgebra.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.MfStarAlgebra


/--
[Corollary_1_43_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_43_5.lean)
-/
@[path]
lemma Corollary_1_43_5
  [DecidableEq ι]
  [Fintype ι]
  {M : MultifusionRingDef ι} :
-- imply
  IsSemisimpleRing (MfGrRingOfC M) :=
-- proof
  M.mf_complexified_semisimple


-- created on 2026-10-23
