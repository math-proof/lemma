import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ} :
-- imply
  sInf (f '' S) = -sSup ((fun x => -f x) '' S) := by
-- proof
  rw [Real.sInf_def, ← Set.image_neg_eq_neg, Set.image_image]


-- created on 2021-09-30
