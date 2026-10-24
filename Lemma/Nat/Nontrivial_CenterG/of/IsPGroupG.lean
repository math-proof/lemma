import Mathlib
import sympy.Basic


namespace PGroups

/--
[p_group_center_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/PGroups.lean)
-/
@[path]
private lemma p_group_center_nontrivial
  [Group G]
  [Finite G]
  [Nontrivial G]
  {p : ℕ} [Fact (Nat.Prime p)]
-- given
  (hG : IsPGroup p G) :
-- imply
  Nontrivial (Subgroup.center G) :=
-- proof
  IsPGroup.center_nontrivial hG

end PGroups


-- created on 2026-10-24
