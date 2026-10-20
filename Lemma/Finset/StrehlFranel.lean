import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.StrehlFranel
open scoped BigOperators
open MetaMathlibExt


/--
[strehl_franel_binomial_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/StrehlFranel.lean)
-/
@[path]
private lemma strehl_franel_binomial_identity_eq
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 * Nat.choose (2 * k) n) =
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 3 := by
-- proof
  apply MetaMathlibExt.strehl_franel_binomial_identity n


-- created on 2026-10-20
