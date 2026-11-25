import Initialize.Tactic.Attr.Basic
import Mathlib


/-- `Fin.natAdd d` is injective. -/
@[path]
private lemma main
-- given
  (d : ℕ) :
-- imply
  Function.Injective (Fin.natAdd d : Fin d → Fin (d + d)) := by
-- proof
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [Fin.natAdd] at this
  omega


-- created on 2026-11-25
