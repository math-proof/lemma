import sympy.stats.linear_td
import sympy.Basic
import Lemma.LinearTDSpec.Any_Ge_0AndAll_LeNormX


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {spec : LinearTDSpec S d} :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ z z' y, ‖spec.update z y - spec.update z' y‖ ≤ C * ‖z - z'‖ := by
-- proof
  obtain ⟨C, hC, h⟩ := LinearTDSpec.Any_Ge_0AndAll_LeNormX (spec := spec)
  refine ⟨(|spec.γ| * C + C) * C, by positivity, fun z z' y => ?_⟩
  have e : spec.update z y - spec.update z' y = (spec.γ * inner ℝ (spec.x y.2) (z - z') - inner ℝ (spec.x y.1) (z - z')) • spec.x y.1 := by
    rw [LinearTDSpec.update, LinearTDSpec.update, ← sub_smul, inner_sub_right, inner_sub_right]
    congr 1
    ring
  have h₁ : |spec.γ * inner ℝ (spec.x y.2) (z - z') - inner ℝ (spec.x y.1) (z - z')| ≤ (|spec.γ| * C + C) * ‖z - z'‖ := by
    calc _ ≤ |spec.γ * inner ℝ (spec.x y.2) (z - z')| + |inner ℝ (spec.x y.1) (z - z')| := abs_sub _ _
      _ ≤ |spec.γ| * (C * ‖z - z'‖) + C * ‖z - z'‖ := by
        rw [abs_mul]
        gcongr
        · exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact h _)
        · exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact h _)
      _ = _ := by ring
  rw [e, norm_smul, Real.norm_eq_abs]
  calc _ ≤ (|spec.γ| * C + C) * ‖z - z'‖ * C := mul_le_mul h₁ (h _) (norm_nonneg _) (by positivity)
    _ = _ := by ring


-- created on 2026-09-26
