import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BAryBinomialCoefficient
open MetaMathlibExt


namespace MetaMathlibExt

/--
[bAryBinomialCoefficient_eq_prod_getD](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialCoefficient.lean)
-/
@[path]
lemma bAryBinomialCoefficient_eq_prod_getD
  {b n k L : ℕ}
-- given
  (hb : 2 ≤ b)
  (hn : (Nat.digits b n).length ≤ L)
  (hk : (Nat.digits b k).length ≤ L) :
-- imply
  bAryBinomialCoefficient b n k hb =
    ∏ i ∈ Finset.range L, ((Nat.digits b n).getD i 0).choose ((Nat.digits b k).getD i 0) := by
-- proof
  rw [bAryBinomialCoefficient, ← List.prod_eq_foldl]
  refine Finset.prod_subset (Finset.range_subset_range.mpr (max_le hn hk)) fun i _ hi => ?_
  rw [Finset.mem_range, not_lt, max_le_iff] at hi
  rw [List.getD_eq_default _ _ hi.1, List.getD_eq_default _ _ hi.2, Nat.choose_self]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
