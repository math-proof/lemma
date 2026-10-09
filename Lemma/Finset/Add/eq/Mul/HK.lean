import sympy.concrete.continuant
import sympy.sets.sets
import sympy.Basic
open Continuant


@[path]
private lemma step2
  {x : ℕ → ℤ}
  {n : ℕ}
-- given
  (h : n ≥ 2) :
-- imply
  H x (n + 1) * K x (n - 1) - H x (n - 1) * K x (n + 1) = (-1) ^ n * x n := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hr : H x (m + 1) * K x m - H x m * K x (m + 1) = (-1) ^ (m + 1) := by
    clear h
    induction m with
    | zero => simp [H, K]
    | succ m ih =>
      rw [H, K, pow_succ, ← ih]
      ring
  rw [show m + 1 - 1 = m by omega, H, K, ← hr]
  ring


-- created on 2020-08-15
