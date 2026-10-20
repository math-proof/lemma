import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.LinearGroupFiniteness
open MathlibExt.GroupTheory.LinearGroupFinitenessWanted


/--
[malcev_residuallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/LinearGroupFiniteness.lean)
-/
@[path]
private lemma malcev_residuallyFinite_eq
  [Field K]
  {n : ℕ}
  {G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)}
-- given
  (hFG : Group.FG G) :
-- imply
  Group.ResiduallyFinite G := by
-- proof
  apply MathlibExt.GroupTheory.LinearGroupFinitenessWanted.malcev_residuallyFinite G hFG


-- created on 2026-10-20
