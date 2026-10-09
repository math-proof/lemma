import sympy.Basic
import sympy.series.limits


@[path]
private lemma main
  {f g : ℝ → ℝ}
-- given
  (h : ∀ x, f x = g x) :
-- imply
  (lim [x → 0] f x / x) = (lim [x → 0] g x / x) := by
-- proof
  have e : (fun x => f x / x) = (fun x => g x / x) := funext fun x => by rw [h x]
  rw [e]


-- created on 2020-05-02
