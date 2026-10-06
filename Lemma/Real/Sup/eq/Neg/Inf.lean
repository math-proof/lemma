import Lemma.Real.Inf.eq.Neg.Sup
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ} :
-- imply
  sSup (f '' S) = -sInf ((fun x => -f x) '' S) := by
-- proof
  have h := Real.Inf.eq.Neg.Sup (S := S) (f := fun x => -f x)
  simp only [neg_neg] at h
  linarith


-- created on 2021-09-30
