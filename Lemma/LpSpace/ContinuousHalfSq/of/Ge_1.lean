import sympy.vector.lp_space
import sympy.Basic
open LpSpace


@[main]
private lemma main
  {p d : ℕ}
-- given
  (h : 1 ≤ p) :
-- imply
  Continuous (half_sq : LpSpace p d → ℝ) := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast h⟩
  unfold half_sq
  fun_prop


-- created on 2026-09-26