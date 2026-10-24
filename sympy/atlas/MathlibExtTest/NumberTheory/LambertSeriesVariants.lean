/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LambertSeriesVariants.lean -/


import sympy.atlas.NumberTheory.LambertSeriesVariants

namespace MetaMathlibExt
example (q : {q : ℂ // ‖q‖ < 1}) (m : {m : ℕ // 1 ≤ m}) :
    tildeLMSummand q m 0 = (q : ℂ) ^ (m : ℕ) / (1 + (q : ℂ)) ^ (2 * (m : ℕ)) := by
  simp [tildeLMSummand]
example (q : {q : ℂ // ‖q‖ < 1}) (m : {m : ℕ // 1 ≤ m}) :
    hatLMSummand q m 0 = (q : ℂ) ^ (m : ℕ) / (1 + (q : ℂ) ^ 2) ^ (m : ℕ) := by
  simp [hatLMSummand]
example (q : {q : ℂ // ‖q‖ < 1}) (m : {m : ℕ // 1 ≤ m}) :
    starLMSummand q m 0 = (q : ℂ) ^ (m : ℕ) / (1 - (q : ℂ)) ^ (2 * (m : ℕ)) := by
  simp [starLMSummand]
example (q : {q : ℂ // ‖q‖ < 1}) (m : {m : ℕ // 1 ≤ m}) :
    tildeLM q m = tsum (tildeLMSummand q m) := rfl
example (q : {q : ℂ // ‖q‖ < 1}) (m : {m : ℕ // 1 ≤ m}) :
    hatLM q m = tsum (hatLMSummand q m) := rfl
example (q : {q : ℂ // ‖q‖ < 1}) (m : {m : ℕ // 1 ≤ m}) :
    starLM q m = tsum (starLMSummand q m) := rfl
end MetaMathlibExt
