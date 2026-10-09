import sympy.core.function
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ} :
-- imply
  Difference (fun x => f x + g x) 1 = fun x => Difference f 1 x + Difference g 1 x := by
-- proof
  funext x
  simp [Difference, fwdDiff]
  ring


-- created on 2020-10-08
