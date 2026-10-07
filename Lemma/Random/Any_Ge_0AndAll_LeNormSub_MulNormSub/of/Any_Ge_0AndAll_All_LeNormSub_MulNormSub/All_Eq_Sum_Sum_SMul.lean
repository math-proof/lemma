import sympy.stats.stochastic_process_types
import sympy.vector.euclidean
import sympy.Basic
import Lemma.Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic
open Finset


@[main]
private lemma main
  {d : ℕ}
  {S : Type*} [Fintype S]
  {F : EuclideanVec d → S × S → EuclideanVec d}
  {f : EuclideanVec d → EuclideanVec d}
  {μ : S → ℝ} [StochasticVec μ]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (h₀ : ∀ w, f w = ∑ s, ∑ s', (μ s * P s s') • F w (s, s'))
  (h₁ : ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖F w y - F w' y‖ ≤ C * ‖w - w'‖) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ := by
-- proof
  have hP : RowStochastic P := inferInstance
  have hμ : StochasticVec μ := inferInstance
  obtain ⟨C, hC, hF⟩ := h₁
  refine ⟨C, hC, fun x y => ?_⟩
  have hw : ∀ s s', 0 ≤ μ s * P s s' := fun s s' => mul_nonneg (hμ.nonneg s) ((hP.stochastic s).nonneg s')
  have hsum : ∑ s, ∑ s', μ s * P s s' = 1 := Matrix.Sum_Mul.eq.One.of.StochasticVec.RowStochastic hP hμ
  rw [h₀, h₀, ← sum_sub_distrib]
  calc _ ≤ ∑ s, ∑ s', μ s * P s s' * (C * ‖x - y‖) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)
        rw [← sum_sub_distrib]
        refine (norm_sum_le _ _).trans (sum_le_sum fun s' _ => ?_)
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hw s s')]
        exact mul_le_mul_of_nonneg_left (hF _ _ _) (hw s s')
    _ = C * ‖x - y‖ := by
        simp_rw [← sum_mul]
        rw [hsum, one_mul]


-- created on 2026-09-26