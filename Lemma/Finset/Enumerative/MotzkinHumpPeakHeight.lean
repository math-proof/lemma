import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MotzkinHumpPeakHeight
open scoped BigOperators
open MetaMathlibExt


/--
[motzkin_hump_peak_height_distribution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinHumpPeakHeight.lean)
-/
@[path]
private lemma motzkin_hump_peak_height_distribution_eq
  {n k : ℕ}
-- given
  (hn : 2 ≤ n)
  (hk : 1 ≤ k) :
-- imply
  let step : Fin 3 → ℤ := by
-- proof
  apply MetaMathlibExt.motzkin_hump_peak_height_distribution n k hn hk


-- created on 2026-10-20
