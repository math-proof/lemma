module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.BooleanFunctions.code.Monotone
open BooleanFourier


public section

/--
[Bool.false_true_of_le_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean)
-/
@[path]
private theorem main
  {a b : Bool}
-- given
  (hle : a ≤ b)
  (hne : a ≠ b) :
-- imply
  a = false ∧ b = true := by
-- proof
  cases a <;> cases b <;> simp [Bool.le_iff_imp] at hle hne ⊢


theorem BooleanFourier.Bool.false_true_of_le_ne
  {a b : Bool}
-- given
  (hle : a ≤ b)
  (hne : a ≠ b) :
-- imply
  a = false ∧ b = true :=
-- proof
  main hle hne


-- created on 2026-10-23
-- updated on 2026-11-24
