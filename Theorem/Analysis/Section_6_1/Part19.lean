module
public import Mathlib
public import Theorem.Analysis.Section_5_1.Part9
public import Theorem.Analysis.Section_5_3.Part12
public import Theorem.Analysis.Section_5_epilogue.Part5
public import Instance.Analysis.Section_6_1.Part6


public section

namespace Chapter6

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

end Chapter6
