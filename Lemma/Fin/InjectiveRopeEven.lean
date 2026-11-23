import Def.Data.Fin.Step
import Initialize.Tactic.Attr.Basic
import Mathlib


/-- The even coordinate `2t` of the interleaved rotary embedding is injective. -/
@[path]
private lemma main
-- given
  (d : ℕ) :
-- imply
  Function.Injective (Fin.stepEven (d := d)) := by
-- proof
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [Fin.stepEven] at this
  omega


-- created on 2026-11-23
