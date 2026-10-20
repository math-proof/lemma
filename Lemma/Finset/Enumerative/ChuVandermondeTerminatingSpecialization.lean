import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.ChuVandermondeTerminatingSpecialization
open scoped BigOperators
open MetaMathlibExt


/--
[chu_vandermonde_terminating_specialization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ChuVandermondeTerminatingSpecialization.lean)
-/
@[path]
private lemma chu_vandermonde_terminating_specialization_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℚ) * ((n + k).choose k : ℚ) * (-1 : ℚ) ^ k / (k + 1) = 0 := by
-- proof
  apply MetaMathlibExt.chu_vandermonde_terminating_specialization n hn


-- created on 2026-10-20
