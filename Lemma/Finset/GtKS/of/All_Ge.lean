import sympy.concrete.continuant_shift
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n ≥ 2)
  (h : ∀ i, 1 ≤ i → i < n + 1 → x i ≥ 1) :
-- imply
  K x (n + 1) > K x n := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hp : ∀ i, 1 ≤ i → i < m + 3 → 0 < x i := fun i h1 h2 => by linarith [h i h1 (by omega)]
  have k1 := K_pos_of x (m + 1) (by omega) (fun i h1 h2 => hp i h1 (by omega))
  have k2 := K_pos_of x (m + 2) (by omega) (fun i h1 h2 => hp i h1 (by omega))
  have hx := h (m + 2) (by omega) (by omega)
  show K x (m + 2) * x (m + 2) + K x (m + 1) > K x (m + 2)
  nlinarith


-- created on 2020-09-16
