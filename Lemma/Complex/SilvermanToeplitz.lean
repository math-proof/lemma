import Mathlib
import sympy.Basic
import sympy.series.SilvermanToeplitz

/--
[SilvermanToeplitz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/SilvermanToeplitz.lean)
-/
@[path]
private lemma silverman_toeplitz_is
-- given
  (A : ℕ → ℕ → ℂ)
  (h_bdd : ∃ C : ℝ, ∀ n, Summable (fun k => ‖A n k‖) ∧ ∑' k, ‖A n k‖ ≤ C)
  (h_col : ∀ k, Filter.Tendsto (fun n => A n k) Filter.atTop (nhds 0))
  (h_sum : Filter.Tendsto (fun n => ∑' k, A n k) Filter.atTop (nhds 1)) :
-- imply
  ∀ (x : ℕ → ℂ) (L : ℂ), Filter.Tendsto x Filter.atTop (nhds L) →
    (∀ n, Summable (fun k => A n k * x k)) ∧
      Filter.Tendsto (fun n => ∑' k, A n k * x k) Filter.atTop (nhds L) := by
-- proof
  apply MetaMathlibExt.silverman_toeplitz A h_bdd h_col h_sum

-- created on 2026-10-10
