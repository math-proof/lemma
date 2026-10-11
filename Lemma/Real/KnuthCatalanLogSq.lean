import Mathlib
import sympy.Basic
import sympy.series.KnuthCatalanLogSq

/--
[KnuthCatalanLogSq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/KnuthCatalanLogSq.lean)
-/
@[path]
private lemma knuth_catalan_log_sq_canonical_is
-- given
  (x : ℝ)
  (hx : |x| ≤ 1 / 4) :
-- imply
  HasSum
    (fun n : ℕ => (Nat.centralBinom (n + 1) : ℝ) *
      (((harmonic (2 * (n + 1) - 1) : ℚ) : ℝ) - ((harmonic (n + 1) : ℚ) : ℝ)) *
      x ^ (n + 1) / ((n : ℝ) + 1))
    ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x ^ n)) ^ 2) := by
-- proof
  apply MetaMathlibExt.knuth_catalan_log_sq_canonical x hx

/--
[KnuthCatalanLogSq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/KnuthCatalanLogSq.lean)
-/
@[path]
private lemma knuth_catalan_log_sq_is
-- given
  (x : ℝ)
  (hx : |x| ≤ 1 / 4) :
-- imply
  HasSum
    (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
      ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
        (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
      x ^ (n + 1) / ((n : ℝ) + 1))
    ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x ^ n)) ^ 2) := by
-- proof
  apply MetaMathlibExt.knuth_catalan_log_sq x hx

-- created on 2026-10-10
