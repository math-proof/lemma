import sympy.Basic
import Theorem.Algebra.BigOperators.Reduced.Part2


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {x : Fin n → ℝ} :
-- imply
  ReducedArgMax (Function.exp x) = ReducedArgMax x := by
-- proof
  refine le_antisymm ?_ ?_
  ·
    apply ReducedArgMax.le_of_forall_le
    intro j
    exact Real.exp_monotone (ReducedArgMax.le x j)
  ·
    apply ReducedArgMax.le_of_forall_le
    intro j
    exact Real.exp_le_exp.mp (ReducedArgMax.le (Function.exp x) j)


-- created on 2021-12-20
