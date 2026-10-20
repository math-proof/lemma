import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.HarmonicPartialSum
open MetaMathlibExt


/--
[harmonic_partial_sum_not_int](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HarmonicPartialSum.lean)
-/
@[path]
private lemma harmonic_partial_sum_not_int_eq
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ ∃ k : ℤ, (k : ℚ) = ∑ ν ∈ Finset.Icc 2 n, harmonic ν := by
-- proof
  apply MetaMathlibExt.harmonic_partial_sum_not_int n hn


-- created on 2026-10-20
