import Lemma.Real.HasDerivAtMulPowAbs
open Real


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ}
-- given
  (h : 2 ≤ n) :
-- imply
  HasDerivAt (fun x : ℝ => n * |x| ^ (n - 2) * x) (n * (n - 1) * |x| ^ (n - 2)) x := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hf : (fun x : ℝ => ((m + 2 : ℕ) : ℝ) * |x| ^ m * x) = fun y => ((m + 2 : ℕ) : ℝ) * (|y| ^ m * y) := by
    funext y
    ring
  rw [hf]
  refine (HasDerivAtMulPowAbs.const_mul _).congr_deriv ?_
  push_cast
  ring


-- created on 2026-09-26