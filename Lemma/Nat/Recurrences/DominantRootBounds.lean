import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.DominantRootBounds
open MetaMathlibExt


/--
[dominant_root_bounds_k_generalized_fibonacci](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/DominantRootBounds.lean)
-/
@[path]
private lemma dominant_root_bounds_k_generalized_fibonacci_eq
  {k : ℕ}
  {α : ℝ}
-- given
  (hα : 1 < α)
  (hroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
-- imply
  (2 - 1 / (k : ℝ) < α ∧ α < 2) ∧
    (4 ≤ k → 2 - 1 / (3 * (k : ℝ)) < α ∧ α < 2) := by
-- proof
  apply MetaMathlibExt.dominant_root_bounds_k_generalized_fibonacci k α hα hroot


-- created on 2026-10-20
