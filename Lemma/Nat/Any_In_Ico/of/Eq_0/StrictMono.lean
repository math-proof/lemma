import sympy.Basic
import Mathlib.Order.Interval.Finset.Nat
open Finset


@[main]
private lemma main
  {t : ℕ → ℕ}
-- given
  (h₀ : StrictMono t)
  (h₁ : t 0 = 0)
  (n : ℕ) :
-- imply
  ∃ m, n ∈ Ico (t m) (t (m + 1)) := by
-- proof
  induction n with
  | zero => exact ⟨0, mem_Ico.2 ⟨h₁.le, by simpa [h₁] using h₀ Nat.zero_lt_one⟩⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    rw [mem_Ico] at hm
    if h : n + 1 < t (m + 1) then
      exact ⟨m, mem_Ico.2 ⟨by omega, h⟩⟩
    else
      exact ⟨m + 1, mem_Ico.2 ⟨by omega, by have := h₀ (show m + 1 < m + 1 + 1 by omega); omega⟩⟩


-- created on 2026-09-26