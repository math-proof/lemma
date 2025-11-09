import stdlib.Slice
import sympy.Basic


@[main]
private lemma main
-- given
  (h_j : j < d)
  (h_start : j < n * d)
  (h_stop : n * d ≤ n * d)
  (h_step : d > 0)
  (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step)[i] = i * d + j := by
-- proof
  -- have := EqLengthGetSlicedIndices.of.Gt_0.LeAddSMul.Lt_AddMul (j := j) (n := n) (n' := n) (by simp [And.intro h_n h_step]) (by simp) h_step
  sorry


-- created on 2025-11-07
-- updated on 2025-11-09
