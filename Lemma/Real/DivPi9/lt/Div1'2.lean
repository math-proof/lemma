import Instance.Analysis.Real.Numbers
import Mathlib.Analysis.Real.Pi.Bounds
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main:
-- imply
  π / 9 < 1 / 2 := by
-- proof
  linarith [Real.pi_lt_four]


-- created on 2025-03-24
-- updated on 2026-10-26
