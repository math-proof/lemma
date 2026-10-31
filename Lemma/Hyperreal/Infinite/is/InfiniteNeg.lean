import Def.Analysis.Real.Limits.Basic
import Initialize.Tactic.Attr.Basic


@[path, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → ∞ ↔ (-x) → ∞ := by
-- proof
  aesop


-- created on 2025-12-10
-- updated on 2026-10-26
