import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BaseBGeneralizedDigitalBinomial
open MetaMathlibExt


/--
[base_b_generalized_digital_binomial_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BaseBGeneralizedDigitalBinomial.lean)
-/
@[path]
private lemma base_b_generalized_digital_binomial_theorem_eq
  {b N n : ℕ}
  {x y : ℝ}
-- given
  (hb : 2 ≤ b)
  (hn : n < b ^ N) :
-- imply
  (∏ i ∈ Finset.range N,
    ((∏ j ∈ Finset.range (n / b ^ i % b), (x + y + (j : ℝ))) /
    ((n / b ^ i % b).factorial : ℝ)) =
    ∑ m ∈ Finset.filter
    (fun m => ∀ i ∈ Finset.range N, m / b ^ i % b ≤ n / b ^ i % b)
    (Finset.range (n + 1)),
    ((∏ i ∈ Finset.range N,
    ((∏ j ∈ Finset.range (m / b ^ i % b), (x + (j : ℝ))) /
    ((m / b ^ i % b).factorial : ℝ))) *
    (∏ i ∈ Finset.range N,
    ((∏ j ∈ Finset.range ((n - m) / b ^ i % b), (y + (j : ℝ))) /
    (((n - m) / b ^ i % b).factorial : ℝ))))) := by
-- proof
  apply MetaMathlibExt.base_b_generalized_digital_binomial_theorem b N n x y hb hn


-- created on 2026-10-20
