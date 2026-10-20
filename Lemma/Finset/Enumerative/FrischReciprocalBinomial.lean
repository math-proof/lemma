import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FrischReciprocalBinomial
open scoped BigOperators
open MetaMathlibExt


/--
[frisch_alternating_reciprocal_binomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FrischReciprocalBinomial.lean)
-/
@[path]
private lemma frisch_alternating_reciprocal_binomial_eq
  {n b c : ℕ}
-- given
  (hc : 0 < c)
  (hcb : c ≤ b) :
-- imply
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹ =
    (c : ℚ) / (n + c) * (Nat.choose (n + b) (b - c) : ℚ)⁻¹ := by
-- proof
  apply MetaMathlibExt.frisch_alternating_reciprocal_binomial n b c hc hcb


-- created on 2026-10-20
