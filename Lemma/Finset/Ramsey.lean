import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Ramsey
open scoped BigOperators
open MathlibExt.Combinatorics.Ramsey


/--
[ramsey_two_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Ramsey.lean)
-/
@[path]
private lemma ramsey_two_uniform_eq
  {r k : ℕ}
-- given
  (hr : 0 < r) :
-- imply
  ∃ N : ℕ, ∀ φ : Finset (Fin N) → Fin r,
    ∃ S : Finset (Fin N), S.card = k ∧ ∃ c : Fin r, ∀ T ∈ S.powersetCard 2, φ T = c := by
-- proof
  apply MathlibExt.Combinatorics.Ramsey.ramsey_two_uniform hr


-- created on 2026-10-20
