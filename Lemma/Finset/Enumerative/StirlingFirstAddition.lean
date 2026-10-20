import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.StirlingFirstAddition
open scoped BigOperators
open MetaMathlibExt


/--
[stirlingFirst_addition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingFirstAddition.lean)
-/
@[path]
private lemma stirlingFirst_addition_eq
  {u v k : ℕ} :
-- imply
  Nat.stirlingFirst (u + v) k =
    ∑ j ∈ Finset.range (v + 1), ∑ i ∈ Finset.range (v + 1),
    v.choose i * u.ascFactorial i * Nat.stirlingFirst (v - i) j *
    (if j ≤ k then Nat.stirlingFirst u (k - j) else 0) := by
-- proof
  apply MetaMathlibExt.stirlingFirst_addition u v k


-- created on 2026-10-20
