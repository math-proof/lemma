import Def.Data.Fin.Rope
import Initialize.Tactic.Attr.Basic
import Mathlib


/-- The odd coordinate `2t + 1` of the interleaved rotary embedding is injective. -/
@[path]
private lemma main
-- given
  (d : ℕ) :
-- imply
  Function.Injective (Fin.ropeOdd (d := d)) := by
-- proof
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [Fin.ropeOdd] at this
  omega


-- created on 2026-11-23
