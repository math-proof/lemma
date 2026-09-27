import Lemma.Real.Eq_0.Lim.of.In_Icc.IsFinite
import Lemma.Real.PowMul.eq.MulPowS
open Filter Topology


@[main]
private lemma main
  {γ : ℝ}
  {x : ℕ → ℝ}
-- given
  (h₀ : γ ∈ Ioo (-1) 0)
  (h₁ : BddAbove (Set.range fun n => |x n|)) :
-- imply
  lim [n → ∞] γ ^ n * x n = 0 := by
-- proof
  let h : ℕ → ℝ := fun n => (-1) ^ n * x n
  have h_def : ∀ n, h n * (-1) ^ n = x n := by
    intro n
    have e : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by
      rw [← Real.PowMul.eq.MulPowS]
      norm_num
    calc h n * (-1) ^ n = ((-1) ^ n * (-1) ^ n) * x n := by simp only [h]; ring
      _ = x n := by rw [e, one_mul]
  have h₂ : BddAbove (Set.range fun n => |h n|) := by
    simpa [h, abs_mul] using h₁
  have h₃ : -γ ∈ Ioo 0 1 := ⟨by linarith [h₀.2], by linarith [h₀.1]⟩
  have h₄ := Real.Eq_0.Lim.of.In_Icc.IsFinite h₃ h₂
  have h₅ : ∀ n, (-γ) ^ n * h n = γ ^ n * x n := by
    intro n
    have e : (-γ) ^ n = (-1) ^ n * γ ^ n := by
      rw [neg_eq_neg_one_mul, Real.PowMul.eq.MulPowS]
    rw [e, ← h_def n]
    ring
  exact h₄.congr h₅


-- created on 2026-09-26
