import Mathlib
import sympy.Basic
import Lemma.AdicCompletion.Support.DVRPadic

open AdicCompletionSupport

/--
[ultrametric_norm_sum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean)
-/
@[path]
private lemma main
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ι : Type*}
  {s : Finset ι}
  {f : ι → ℚ_[p]}
  {C : ℝ}
-- given
  (hC : 0 < C)
  (hbound : ∀ i ∈ s, ‖f i‖ < C) :
-- imply
  ‖∑ i ∈ s, f i‖ < C := by
-- proof
  apply ultrametric_norm_sum_lt p hC hbound


-- created on 2026-10-23
