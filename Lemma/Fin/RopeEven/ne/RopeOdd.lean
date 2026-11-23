import Def.Data.Fin.Rope
import Initialize.Tactic.Attr.Basic
import Mathlib


/-- An even interleaved coordinate never equals an odd one. -/
@[path]
private lemma main
-- given
  (d : ℕ)
  (t s : Fin d) :
-- imply
  t.ropeEven ≠ s.ropeOdd := by
-- proof
  intro h
  have := congrArg Fin.val h
  simp [Fin.ropeEven, Fin.ropeOdd] at this
  omega


-- created on 2026-11-23
