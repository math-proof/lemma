import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {t : ℕ}
  {s sprev G x : ℝ}
-- given
  (h₀ : 0 < t)
  (h₁ : s = G + sprev + x) :
-- imply
  s - sprev = G + x ∧ 0 < t := by
-- proof
  constructor
  ·
    rw [h₁]
    ring
  ·
    exact h₀


-- created on 2020-12-17
-- updated on 2026-10-26
