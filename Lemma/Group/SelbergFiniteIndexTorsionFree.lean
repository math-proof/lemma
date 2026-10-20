import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.SelbergFiniteIndexTorsionFree
open MathlibExt.GroupTheory.LinearGroupFinitenessWanted


/--
[selberg_finiteIndex_torsionFree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SelbergFiniteIndexTorsionFree.lean)
-/
@[path]
private lemma selberg_finiteIndex_torsionFree_eq
  [Field K] [CharZero K]
  {n : ℕ}
  {G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)}
-- given
  (hFG : Group.FG G) :
-- imply
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsMulTorsionFree H := by
-- proof
  apply MathlibExt.GroupTheory.LinearGroupFinitenessWanted.selberg_finiteIndex_torsionFree G hFG


-- created on 2026-10-20
