import Mathlib
import sympy.Basic
open Set


namespace ContinuousFunctions

/--
[intermediate_value_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/IVT.lean)
-/
@[path]
lemma intermediate_value_theorem
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a < b)
  (hf : ContinuousOn f (Set.Icc a b)) :
-- imply
  (∀ y, f a < y → y < f b → ∃ c ∈ Set.Ioo a b, f c = y) ∧ (∀ y, f b < y → y < f a → ∃ c ∈ Set.Ioo a b, f c = y) := by
-- proof
  have hab' : a ≤ b := le_of_lt hab
  constructor
  · intro y hy1 hy2
    have hy_mem : y ∈ Icc (f a) (f b) := ⟨le_of_lt hy1, le_of_lt hy2⟩
    obtain ⟨c, hc_mem, hfc⟩ := intermediate_value_Icc hab' hf hy_mem
    refine ⟨c, ?_, hfc⟩
    constructor
    · rcases eq_or_lt_of_le hc_mem.1 with h | h
      · exfalso; linarith [hfc ▸ h ▸ hy1]
      · exact h
    · rcases eq_or_lt_of_le hc_mem.2 with h | h
      · exfalso; linarith [hfc ▸ h ▸ hy2]
      · exact h
  · intro y hy1 hy2
    have hy_mem : y ∈ Icc (f b) (f a) := ⟨le_of_lt hy1, le_of_lt hy2⟩
    obtain ⟨c, hc_mem, hfc⟩ := intermediate_value_Icc' hab' hf hy_mem
    refine ⟨c, ?_, hfc⟩
    constructor
    · rcases eq_or_lt_of_le hc_mem.1 with h | h
      · exfalso; linarith [hfc ▸ h ▸ hy2]
      · exact h
    · rcases eq_or_lt_of_le hc_mem.2 with h | h
      · exfalso; linarith [hfc ▸ h ▸ hy1]
      · exact h

end ContinuousFunctions

namespace ContinuousFunctions

/--
[polynomial_has_real_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/IVT.lean)
-/
@[path]
lemma polynomial_has_real_root
-- imply
  ∃ x : ℝ, x^2021 + x^2020 + 9.03*x + 1 = 0 := by
-- proof
  let f : ℝ → ℝ := fun x => x^2021 + x^2020 + 9.03*x + 1
  have hf_cont : Continuous f := by fun_prop
  have hf_neg : f (-1) < 0 := by norm_num [f]
  have hf_pos : (0 : ℝ) < f 0 := by norm_num [f]
  have hab : (-1 : ℝ) ≤ 0 := by norm_num
  have h0_mem : (0 : ℝ) ∈ Icc (f (-1)) (f 0) :=
    ⟨le_of_lt hf_neg, le_of_lt hf_pos⟩
  have h_ivt := intermediate_value_Icc hab hf_cont.continuousOn h0_mem
  obtain ⟨c, _, hfc⟩ := h_ivt
  exact ⟨c, hfc⟩

end ContinuousFunctions


-- created on 2026-10-23
