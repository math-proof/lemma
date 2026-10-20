import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.AmenableGroup
open scoped Pointwise Classical symmDiff


/--
[isAmenable_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AmenableGroup.lean)
-/
@[path]
private lemma isAmenable_of_finite_eq
  [Group G] [Finite G] :
-- imply
  IsAmenable G := by
-- proof
  apply isAmenable_of_finite G

/--
[isAmenable_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AmenableGroup.lean)
-/
@[path]
private lemma isAmenable_of_subsingleton_eq
  [Group G] [Subsingleton G] :
-- imply
  IsAmenable G := by
-- proof
  apply isAmenable_of_subsingleton G


-- created on 2026-10-20
