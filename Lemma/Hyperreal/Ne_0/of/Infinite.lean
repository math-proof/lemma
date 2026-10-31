import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ*}
-- given
  (h : x → ∞) :
-- imply
  x ≠ 0 := by
-- proof
  contrapose! h
  subst h
  simp


-- created on 2025-12-17
