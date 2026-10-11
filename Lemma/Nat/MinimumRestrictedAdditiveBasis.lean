import Mathlib
import sympy.Basic
import sympy.combinatorics.additive.MinimumRestrictedAdditiveBasis


/--
[MinimumRestrictedAdditiveBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/MinimumRestrictedAdditiveBasis.lean)
-/
@[path]
private lemma minimum_restricted_additive_basis_card_eq_none_iff_iff
-- given
  (s : ℕ) :
-- imply
  (MetaMathlibExt.minimumRestrictedAdditiveBasisCard s).val = none ↔ s % 2 = 1 := by
-- proof
  apply MetaMathlibExt.minimumRestrictedAdditiveBasisCard_eq_none_iff s

/--
[MinimumRestrictedAdditiveBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/MinimumRestrictedAdditiveBasis.lean)
-/
@[path]
private lemma minimum_restricted_additive_basis_card_is_some_iff_iff
-- given
  (s : ℕ) :
-- imply
  (MetaMathlibExt.minimumRestrictedAdditiveBasisCard s).val.isSome ↔ s % 2 = 0 := by
-- proof
  apply MetaMathlibExt.minimumRestrictedAdditiveBasisCard_isSome_iff s


-- created on 2026-10-11
