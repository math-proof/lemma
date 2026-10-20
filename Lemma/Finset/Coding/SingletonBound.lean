import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Coding.SingletonBound
open MathlibExt.Combinatorics.Coding.SingletonBound


/--
[singleton_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Coding/SingletonBound.lean)
-/
@[path]
private lemma singleton_bound_eq
  [Fintype α] [DecidableEq α] [Nonempty α]
  {n d : ℕ}
  {C : Finset (Fin n → α)}
-- given
  (hd1 : 1 ≤ d)
  (hd2 : d ≤ n)
  (hDist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
-- imply
  C.card ≤ (Fintype.card α) ^ (n - d + 1) := by
-- proof
  apply MathlibExt.Combinatorics.Coding.SingletonBound.singleton_bound C hd1 hd2 hDist


-- created on 2026-10-20
