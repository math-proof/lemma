import sympy.concrete.continuant_shift
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (_h₀ : n > 0)
  (h : ∀ i, x i > 0) :
-- imply
  K (fun i => x (i + 1)) n / H (fun i => x (i + 1)) n = H x (n + 1) / K x (n + 1) - x 0 := by
-- proof
  rw [K_succ_eq_H_shift, H_succ_eq, K_succ_eq_H_shift]
  have hH := H_pos_of_lt (fun i => x (i + 1)) n (fun i _ => h (i + 1))
  field_simp
  ring


-- created on 2026-09-27
