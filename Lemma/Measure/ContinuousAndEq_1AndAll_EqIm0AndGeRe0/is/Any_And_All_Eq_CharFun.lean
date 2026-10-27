import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Fourier.Bochner.Part3

open Fourier.BochnerWanted
open MeasureTheory

/--
[bochner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/Bochner.lean)
-/
@[path]
private lemma bochner_iff
-- given
  {f : ℝ → ℂ} :
-- imply
  (Continuous f ∧ f 0 = 1 ∧
    ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
      let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
      S.im = 0 ∧ 0 ≤ S.re)
  ↔
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ t : ℝ, f t = charFun μ t := by
-- proof
  apply bochner

-- created on 2026-10-10
