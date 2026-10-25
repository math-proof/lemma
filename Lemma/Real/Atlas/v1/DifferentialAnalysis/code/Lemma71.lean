import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.Lemma71
open SchwartzMap TemperedDistributions
open scoped SchwartzMap


namespace TemperedDistributions

/--
[schwartz_iff_weightedDeriv_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma71.lean)
-/
@[path]
lemma schwartz_iff_weightedDeriv_bounded
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {f : E → F}
-- given
  (hsmooth : ContDiff ℝ (⊤ : ℕ∞) f) :
-- imply
  (∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) ↔ (∀ k n : ℕ, n ≤ k → ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) := by
-- proof
  constructor
  ·
    intro hdecay k n _hn
    let g : 𝓢(E, F) := ⟨f, hsmooth, hdecay⟩
    exact ⟨2 ^ k * (Finset.Iic ((k, n) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g,
      fun x => SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (k, n)) le_rfl le_rfl g x⟩
  ·
    intro hdecay j n
    obtain ⟨C, hC⟩ := hdecay (max j n) n (le_max_right j n)
    exact ⟨C, fun x => calc
      ‖x‖ ^ j * ‖iteratedFDeriv ℝ n f x‖
        ≤ (1 + ‖x‖) ^ j * ‖iteratedFDeriv ℝ n f x‖ := by
          gcongr; linarith [norm_nonneg x]
      _ ≤ (1 + ‖x‖) ^ max j n * ‖iteratedFDeriv ℝ n f x‖ := by
        gcongr
        · linarith [norm_nonneg x]
        · exact le_max_left j n
      _ ≤ C := hC x⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartz_weightedDeriv_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma71.lean)
-/
@[path]
lemma schwartz_weightedDeriv_bounded
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {f : 𝓢(E, F)}
  {k n : ℕ} :
-- imply
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C := by
-- proof
  refine ⟨2 ^ k * (Finset.Iic ((k, n) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, by positivity, fun x => ?_⟩
  exact SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (k, n)) le_rfl le_rfl f x
end TemperedDistributions



-- created on 2026-10-23
