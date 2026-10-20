import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RefinedEulerianMarginals
open MetaMathlibExt


/--
[sun_refined_eulerian_marginals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RefinedEulerianMarginals.lean)
-/
@[path]
private lemma sun_refined_eulerian_marginals_eq
  {n : ℕ}
  {p q : ℝ}
-- given
  (hn : 0 < n) :
-- imply
  let odes : Equiv.Perm (Fin n) → ℕ := by
-- proof
  apply MetaMathlibExt.sun_refined_eulerian_marginals n hn p q


-- created on 2026-10-20
