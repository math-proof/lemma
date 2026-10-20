import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CatalanHarmonicGeneratingFunction
open scoped BigOperators
open MetaMathlibExt


/--
[catalan_harmonic_generating_function_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma catalan_harmonic_generating_function_canonical_eq
  {x : ℝ}
-- given
  (hx : |x| < 1 / 4) :
-- imply
  (∑' n : ℕ, (catalan n : ℝ) * ((harmonic n : ℚ) : ℝ) * x ^ (n + 1)) =
    Real.log 2 +
    Real.sqrt (1 - 4 * x) * Real.log (2 * Real.sqrt (1 - 4 * x)) -
    (1 + Real.sqrt (1 - 4 * x)) * Real.log (1 + Real.sqrt (1 - 4 * x)) := by
-- proof
  apply MetaMathlibExt.catalan_harmonic_generating_function_canonical x hx

/--
[catalan_harmonic_generating_function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma catalan_harmonic_generating_function_eq
  {x : ℝ}
-- given
  (hx : |x| < 1 / 4) :
-- imply
  (∑' n : ℕ,
    if n = 0 then 0
    else
    (((Nat.choose (2 * n) n / (n + 1) : ℕ) : ℝ) *
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ)⁻¹)) * x ^ (n + 1))) =
    Real.log 2 +
    Real.sqrt (1 - 4 * x) * Real.log (2 * Real.sqrt (1 - 4 * x)) -
    (1 + Real.sqrt (1 - 4 * x)) * Real.log (1 + Real.sqrt (1 - 4 * x)) := by
-- proof
  apply MetaMathlibExt.catalan_harmonic_generating_function x hx


-- created on 2026-10-20
