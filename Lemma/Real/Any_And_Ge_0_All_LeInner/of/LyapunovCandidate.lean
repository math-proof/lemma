import sympy.stats.lyapunov
import sympy.Basic
open Finset


@[main]
private lemma main
  {d : ℕ}
  {φ : EuclideanVec d → ℝ}
  {φ' : EuclideanVec d → EuclideanVec d}
-- given
  (h : LyapunovCandidate φ φ') :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ x y, inner ℝ (φ' x) y ≤ C * √(φ x) * √(φ y) := by
-- proof
  obtain ⟨C, hC, hC'⟩ := h.inner_grad_le'
  refine ⟨C, hC, fun x y => le_trans ?_ (hC' x y)⟩
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact sum_le_sum fun i _ => (le_abs_self _).trans_eq (by rw [abs_mul]; ring)


-- created on 2026-09-26