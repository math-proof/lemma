import Lemma.Real.Minima.eq.Neg.Maxima
import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ} :
-- imply
  Maxima S f = -Minima S (fun x => -f x) := by
-- proof
  have hm := Real.Minima.eq.Neg.Maxima (S := S) (f := fun x => -f x)
  have hff : (fun x : ℝ => -(-f x)) = f := by
    funext x
    ring
  rw [hff] at hm
  linarith


-- created on 2021-09-30
