import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  Set.Ico x y ⊆ Set.Ico x (|y|) := by
-- proof
  intro z hz
  exact ⟨hz.1, hz.2.trans_le (le_abs_self y)⟩


-- created on 2019-07-09
