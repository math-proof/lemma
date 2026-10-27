import Mathlib
import Initialize.Tactic.Attr.Basic


namespace QuotientGroups

/--
[quotient_group_composition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/QuotientGroups.lean)
-/
@[path]
private lemma quotient_group_composition
  [Group G]
  {N : Subgroup G} [N.Normal] :
-- imply
  Function.Surjective (QuotientGroup.mk' N) ∧ MonoidHom.ker (QuotientGroup.mk' N) = N :=
-- proof
  ⟨QuotientGroup.mk'_surjective N, QuotientGroup.ker_mk' N⟩

end QuotientGroups


-- created on 2026-10-24
