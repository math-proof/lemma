import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S]
-- given
  (x : S → ℝ) :
-- imply
  ‖x‖ ≤ ∑ i, |x i| := by
-- proof
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)


-- created on 2026-09-26
