import sympy.core.function
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {m d : ℕ}
-- given
  (h : m ≤ d) :
-- imply
  Difference f d = Difference (Difference f m) (d - m) := by
-- proof
  funext x
  simp only [Difference]
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]


-- created on 2020-10-08
