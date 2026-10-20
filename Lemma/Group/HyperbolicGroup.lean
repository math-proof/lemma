import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.HyperbolicGroup
open Group


/--
[IsHyperbolic.fg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HyperbolicGroup.lean)
-/
@[path]
private lemma IsHyperbolic_fg_eq
  [Group G]
-- given
  (h : IsHyperbolic G) :
-- imply
  Group.FG G := by
-- proof
  apply Group.IsHyperbolic.fg h

/--
[IsHyperbolic.of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HyperbolicGroup.lean)
-/
@[path]
private lemma IsHyperbolic_of_subsingleton_eq
  [Group G] [Subsingleton G] :
-- imply
  IsHyperbolic G := by
-- proof
  apply Group.IsHyperbolic.of_subsingleton G


-- created on 2026-10-20
