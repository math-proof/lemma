import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.Convergence
open MetaMathlibExt.MultipleZeta


/--
[summable_strictSummand](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Convergence.lean)
-/
@[path]
private lemma summable_strictSummand_eq
  {index : Index}
-- given
  (hindex : index.IsAdmissible) :
-- imply
  Summable (strictSummand index) := by
-- proof
  apply MetaMathlibExt.MultipleZeta.summable_strictSummand index hindex


-- created on 2026-10-20
