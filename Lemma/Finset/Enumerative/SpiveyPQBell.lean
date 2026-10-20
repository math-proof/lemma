import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.SpiveyPQBell
open scoped BigOperators
open MetaMathlibExt


/--
[spivey_pq_bell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean)
-/
@[path]
private lemma spivey_pq_bell_eq
  :
-- imply
  ∀ (p q : ℝ) (hq0 : 0 < q) (hqp : q < p) (hp1 : p ≤ 1),
    let bracket : ℕ → ℝ := by
-- proof
  apply MetaMathlibExt.spivey_pq_bell


-- created on 2026-10-20
