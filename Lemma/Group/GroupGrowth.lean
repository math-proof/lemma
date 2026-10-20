import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.GroupGrowth
open Group.Generators


/--
[hasPolynomialGrowth_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupGrowth.lean)
-/
@[path]
private lemma hasPolynomialGrowth_of_finite_eq
  [Group G] [Finite G]
  {P : Group.Generators G ι} :
-- imply
  P.HasPolynomialGrowth := by
-- proof
  apply Group.Generators.hasPolynomialGrowth_of_finite P


-- created on 2026-10-20
