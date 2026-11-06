import Mathlib.Data.EReal.Basic
import Initialize.Tactic.Attr.Basic
open EReal


/--
If `a` is bounded above by `-t` for every real `t` with `↑t < b`, then `a ≤ -b`.
-/
@[path]
private lemma main
  {a b : EReal}
-- given
  (h : ∀ t : ℝ, ↑t < b → a ≤ -↑t) :
-- imply
  a ≤ -b := by
-- proof
  cases b with
  | bot =>
    exact le_top.trans_eq EReal.neg_bot.symm
  | top =>
    cases a with
    | bot =>
      rw [EReal.neg_top]
    | coe q =>
      exfalso
      have hq : ((-q + 1 : ℝ) : EReal) < ⊤ := EReal.coe_lt_top (-q + 1)
      have hle := h (-q + 1) hq
      rw [← EReal.coe_neg, EReal.coe_le_coe_iff] at hle
      linarith
    | top =>
      exfalso
      have hle := h 0 (EReal.coe_lt_top 0)
      rw [← EReal.coe_neg] at hle
      exact not_le_of_gt (EReal.coe_lt_top _) hle
  | coe r =>
    cases a with
    | bot => exact bot_le
    | top =>
      exfalso
      have hle := h (r - 1) (EReal.coe_lt_coe_iff.mpr (by linarith))
      rw [← EReal.coe_neg] at hle
      exact not_le_of_gt (EReal.coe_lt_top _) hle
    | coe q =>
      rw [← EReal.coe_neg, EReal.coe_le_coe_iff]
      by_contra hqr
      push Not at hqr
      have hlt : -q < r := by linarith
      obtain ⟨t, ht1, ht2⟩ := exists_between hlt
      have hle := h t (EReal.coe_lt_coe_iff.mpr ht2)
      rw [← EReal.coe_neg, EReal.coe_le_coe_iff] at hle
      linarith


-- created on 2026-11-05
