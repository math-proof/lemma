import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.StaverReciprocalBinomialSum
open MetaMathlibExt


/--
[staver_reciprocal_binomial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StaverReciprocalBinomialSum.lean)
-/
@[path]
private lemma staver_reciprocal_binomial_sum_eq
  {n : Nat} :
-- imply
  (Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹) =
    ((n + 1 : Rat) / (2 : Rat) ^ (n + 1)) *
    (Finset.Icc 1 (n + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat)) := by
-- proof
  apply MetaMathlibExt.staver_reciprocal_binomial_sum n


-- created on 2026-10-20
