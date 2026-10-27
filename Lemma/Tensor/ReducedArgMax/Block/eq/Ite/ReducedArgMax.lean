import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.BigOperators.Reduced.Part2


@[path]
private lemma main
  {m n : ℕ} [NeZero m] [NeZero n]
  {x : Fin m → ℝ}
  {y : Fin n → ℝ} :
-- imply
  ReducedArgMax (Fin.append x y) =
    if Function.max y > Function.max x then Fin.natAdd m (ReducedArgMax y)
    else Fin.castAdd n (ReducedArgMax x) := by
-- proof
  apply ReducedArgMax.append_eq_ite


-- created on 2022-01-03
