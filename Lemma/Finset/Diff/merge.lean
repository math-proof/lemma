import sympy.core.function
import sympy.Basic


@[main]
private lemma main
  {f : ℝ → ℝ}
  {d n : ℕ}
-- given
  (h : d ≤ n) :
-- imply
  Difference (Difference f d) (n - d) = Difference f n := by
-- proof
  funext x
  simp only [Difference]
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]


-- created on 2020-10-12
