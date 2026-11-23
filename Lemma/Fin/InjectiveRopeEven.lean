import Def.Data.Fin.Rope
import Initialize.Tactic.Attr.Basic
import Mathlib


/-- The even coordinate `2t` of the interleaved rotary embedding is injective. -/
@[path]
private lemma main
-- given
  (d : ℕ) :
-- imply
  Function.Injective (Fin.ropeEven (d := d)) := by
-- proof
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [Fin.ropeEven] at this
  omega


-- created on 2026-11-23
