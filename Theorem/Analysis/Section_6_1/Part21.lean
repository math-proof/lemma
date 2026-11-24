module
public import Mathlib
public import Theorem.Analysis.Section_5_1.Part9
public import Theorem.Analysis.Section_5_3.Part12
public import Theorem.Analysis.Section_5_epilogue.Part5
public import Instance.Analysis.Section_6_1.Part8


public section

namespace Chapter6

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

end Chapter6
