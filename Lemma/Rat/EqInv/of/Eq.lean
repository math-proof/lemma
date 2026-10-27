import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
  -- given
  (h : a = b)
  -- imply
  : a⁻¹ = b⁻¹ := by
  -- proof
  exact congr_arg Inv.inv h

-- created on 2021-08-16
