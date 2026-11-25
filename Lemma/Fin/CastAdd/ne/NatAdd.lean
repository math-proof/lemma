import Initialize.Tactic.Attr.Basic
import Mathlib


/-- `Fin.castAdd` and `Fin.natAdd` land in disjoint halves. -/
@[path]
private lemma main
  {d : ℕ}
-- given
  (t s : Fin d) :
-- imply
  t.castAdd d ≠ s.natAdd d := by
-- proof
  intro h
  have := congrArg Fin.val h
  simp [Fin.castAdd, Fin.natAdd] at this
  have := t.isLt
  omega


-- created on 2026-11-25
