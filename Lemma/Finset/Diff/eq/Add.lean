import sympy.core.function
import sympy.Basic


@[path]
private lemma main
  {d : ℕ}
  {f g : ℝ → ℝ} :
-- imply
  Difference (fun x => f x + g x) d = fun x => Difference f d x + Difference g d x := by
-- proof
  induction d with
  | zero =>
    rfl
  | succ d ih =>
    funext x
    simp only [Difference, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]
    simp [fwdDiff]
    ring


-- created on 2020-10-09
