import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Sequences.GeneratingFunctionTermExtraction
open MetaMathlibExt


/--
[generating_function_term_extraction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Sequences/GeneratingFunctionTermExtraction.lean)
-/
@[path]
private lemma generating_function_term_extraction_eq
  {t : ℕ → ℕ}
  {c m N : ℕ}
-- given
  (hc : 2 ≤ c)
  (hm : 2 ≤ m)
  (hmN : m ≤ N)
  (hconv : Summable (fun k : ℕ => (t k : ℝ) * (((c : ℝ) ^ N)⁻¹) ^ k))
  (hbound : ∀ j, m ≤ j → t j < c ^ (j - 2)) :
-- imply
  t N = Nat.floor ((c : ℝ) ^ (N ^ 2) *
    (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ N)⁻¹) ^ k)) % c ^ N := by
-- proof
  apply MetaMathlibExt.generating_function_term_extraction t c m N hc hm hmN hconv hbound


-- created on 2026-10-20
