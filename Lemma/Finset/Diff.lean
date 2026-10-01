import sympy.core.function
import sympy.Basic


@[main]
private lemma merge
  {f : ℝ → ℝ}
  {d m : ℕ} :
-- imply
  Difference (Difference f d) m = Difference f (m + d) :=
-- proof
  (Function.iterate_add_apply _ m d f).symm


@[main]
private lemma split
  {f : ℝ → ℝ}
  {d m : ℕ}
-- given
  (h : m ≤ d) :
-- imply
  Difference f d = Difference (Difference f m) (d - m) := by
-- proof
  unfold Difference
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel h]


-- created on 2020-10-12
