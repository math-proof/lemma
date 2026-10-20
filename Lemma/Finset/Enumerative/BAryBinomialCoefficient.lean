import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BAryBinomialCoefficient
open MetaMathlibExt


/--
[bAryBinomialCoefficient_eq_prod_getD](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialCoefficient.lean)
-/
@[path]
private lemma bAryBinomialCoefficient_eq_prod_getD_eq
  {b n k L : ℕ}
-- given
  (hb : 2 ≤ b)
  (hn : (Nat.digits b n).length ≤ L)
  (hk : (Nat.digits b k).length ≤ L) :
-- imply
  bAryBinomialCoefficient b n k hb =
    ∏ i ∈ Finset.range L, ((Nat.digits b n).getD i 0).choose ((Nat.digits b k).getD i 0) := by
-- proof
  apply MetaMathlibExt.bAryBinomialCoefficient_eq_prod_getD b n k hb hn hk


-- created on 2026-10-20
