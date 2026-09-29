import Mathlib.Analysis.SpecialFunctions.Exp

/-- py `exp(a + (m - 1) * oo)` for a mask entry `m ∈ {0, 1}`: `exp a` where `m = 1`, `0` elsewhere.
The `−∞` logit itself is not represented: a masked entry is dropped (its exponential is `0`). -/
noncomputable def maskedExp (a m : ℝ) : ℝ :=
  if m = 1 then Real.exp a else 0

/-- py `softmax(a + (mask - 1) * oo)` over the last axis: exponentiate only the positions with
`mask = 1`, put `0` elsewhere, and normalize over the unmasked positions. -/
noncomputable def maskedSoftmax (a mask : Fin n → ℝ) : Fin n → ℝ :=
  fun j => maskedExp (a j) (mask j) / ∑ k, maskedExp (a k) (mask k)


-- created on 2026-09-27
