import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : -x < y) :
-- imply
  |x| < y := by
-- proof
  exact abs_lt.mpr ⟨by linarith, h₀⟩


-- created on 2019-12-30
