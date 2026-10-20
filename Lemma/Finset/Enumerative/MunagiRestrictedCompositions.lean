import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MunagiRestrictedCompositions
open MetaMathlibExt


/--
[munagi_restricted_compositions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MunagiRestrictedCompositions.lean)
-/
@[path]
private lemma munagi_restricted_compositions_eq
  {n k : ℕ}
-- given
  (hn : 0 < n)
  (hk : 0 < k) :
-- imply
  Fintype.card {c : Composition n // ∀ a ∈ c.blocks, a % k = 1 % k} =
    Fintype.card {c : Composition (n + k - 1) // ∀ a ∈ c.blocks, k ≤ a} := by
-- proof
  apply MetaMathlibExt.munagi_restricted_compositions n k hn hk


-- created on 2026-10-20
