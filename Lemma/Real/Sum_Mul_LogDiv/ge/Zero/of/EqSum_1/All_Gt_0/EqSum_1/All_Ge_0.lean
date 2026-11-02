import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Initialize.Tactic.Attr.Basic
open Finset Real


private lemma ge_0 [Fintype α] {ν m : α → ℝ} (hν : ∀ a, 0 ≤ ν a) (hsumν : ∑ a, ν a = 1) (hm : ∀ a, 0 < m a) (hsumm : ∑ a, m a = 1) :
  0 ≤ ∑ a, ν a * log (ν a / m a) := by
  have hterm : ∀ a, ν a - m a ≤ ν a * log (ν a / m a) := by
    intro a
    obtain h0 | hpos := eq_or_lt_of_le (hν a)
    ·
      simp [← h0]
      linarith [hm a]
    ·
      have hineq := log_le_sub_one_of_pos (div_pos (hm a) hpos)
      have hmul := mul_le_mul_of_nonneg_left hineq hpos.le
      have hright : ν a * (m a / ν a - 1) = m a - ν a := by
        field_simp [hpos.ne']
      have hlog : ν a * log (ν a / m a) = -(ν a * log (m a / ν a)) := by
        rw [← inv_div, log_inv (m a / ν a), mul_neg]
      rw [hlog]
      rw [hright] at hmul
      linarith
  calc
    _ = ∑ a, ν a - ∑ a, m a := by simp [hsumν, hsumm]
    _ = ∑ a, (ν a - m a) := by rw [← sum_sub_distrib]
    _ ≤ ∑ a, ν a * log (ν a / m a) := sum_le_sum fun a _ => hterm a

/--
Relative entropy of a probability vector against a positive probability vector is nonnegative.
-/
@[path]
private lemma main
  [Fintype α]
  {ν m : α → ℝ}
-- given
  (hν : ∀ a, 0 ≤ ν a)
  (hsumν : ∑ a, ν a = 1)
  (hm : ∀ a, 0 < m a)
  (hsumm : ∑ a, m a = 1) :
-- imply
  0 ≤ ∑ a, ν a * log (ν a / m a) :=
-- proof
  ge_0 hν hsumν hm hsumm


-- created on 2026-11-02
