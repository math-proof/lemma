import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  Set.Ioc (|x|) y ⊆ Set.Ioc x y := by
-- proof
  intro z hz
  exact ⟨(le_abs_self x).trans_lt hz.1, hz.2⟩


-- created on 2019-09-06
