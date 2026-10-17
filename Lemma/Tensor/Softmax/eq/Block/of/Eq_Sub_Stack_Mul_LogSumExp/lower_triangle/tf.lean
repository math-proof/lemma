import Mathlib.Analysis.SpecialFunctions.Exp
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {A : Matrix (Fin n) (Fin n) ℝ}
  {l : ℕ}
-- given
  (h₀ : 1 ≤ l) :
-- imply
  ∀ i, ∑ j, (if j ≤ i ∧ i.val < j.val + l then Real.exp (A i j) else 0) /
      ∑ k, (if k ≤ i ∧ i.val < k.val + l then Real.exp (A i k) else 0) = 1 := by
-- proof
  intro i
  rw [← Finset.sum_div]
  refine div_self (ne_of_gt (Finset.sum_pos' (fun k _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩))
  ·
    split
    · exact le_of_lt (Real.exp_pos _)
    · exact le_rfl
  ·
    have hdiag : i ≤ i ∧ i.val < i.val + l := by
      constructor
      · exact le_rfl
      · omega
    simp [hdiag, Real.exp_pos]


-- created on 2026-10-11
-- updated on 2026-10-17
