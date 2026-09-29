import sympy.concrete.continuant_shift
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, 1 ≤ i → i < n + 1 → x i ≥ 1) :
-- imply
  K x (n + 1) ≥ K x n := by
-- proof
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl : n = 1 := by omega
    have := h 1 le_rfl (by omega)
    show K x 1 * x 1 + K x 0 ≥ K x 1
    rw [show K x 1 = 1 from rfl, show K x 0 = 0 from rfl]
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    apply le_of_lt
    have hp : ∀ i, 1 ≤ i → i < m + 3 → 0 < x i := fun i h1 h2 => by linarith [h i h1 (by omega)]
    have k1 := K_pos_of x (m + 1) (by omega) (fun i h1 h2 => hp i h1 (by omega))
    have k2 := K_pos_of x (m + 2) (by omega) (fun i h1 h2 => hp i h1 (by omega))
    have hx := h (m + 2) (by omega) (by omega)
    show K x (m + 2) * x (m + 2) + K x (m + 1) > K x (m + 2)
    nlinarith


-- created on 2026-09-27
