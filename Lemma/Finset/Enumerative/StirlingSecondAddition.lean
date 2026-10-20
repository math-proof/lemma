import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.StirlingSecondAddition
open MetaMathlibExt


/--
[stirlingSecond_addition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondAddition.lean)
-/
@[path]
private lemma stirlingSecond_addition_eq
  {u v k : ℕ}
-- given
  (hu : 0 < u) :
-- imply
  Nat.stirlingSecond (u + v) k =
    ∑ n ∈ Finset.Icc 1 k, Nat.stirlingSecond u n *
    ∑ m ∈ Finset.Icc (k - n) v,
    Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m) := by
-- proof
  apply MetaMathlibExt.stirlingSecond_addition u v k hu


-- created on 2026-10-20
