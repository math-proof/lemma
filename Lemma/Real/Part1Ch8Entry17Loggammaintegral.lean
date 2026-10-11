import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch8Entry17Loggammaintegral

open Ramanujan.Part1Ch8.Entry17Loggammaintegral

/--
[Part1Ch8Entry17Loggammaintegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry17Loggammaintegral.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry17_log_gamma_integral_eq
-- given
  (x : ℝ)
  (n : ℕ)
  (hx : -1 < x)
  (hn : 0 < n) :
-- imply
  (∀ j : ℕ, 0 < (j + 1 : ℝ) + x) ∧
    (∀ k ∈ Finset.range n, ∀ j : ℕ, 0 < (j + 1 : ℝ) + (x - k) / n) ∧
    Summable (chapter8Entry17Term x) ∧
    (∀ k ∈ Finset.range n, Summable (chapter8Entry17Term ((x - k) / n))) ∧
    0 < Real.Gamma (x + 1) ∧
    (n : ℝ) * chapter8Entry17Phi x - ∑ k ∈ Finset.range n, chapter8Entry17Phi ((x - k) / n) =
      (n : ℝ) * Real.log n * chapter8RealDigamma (x + 1) - (n : ℝ) * Real.log n ^ 2 / 2 := by
-- proof
  apply Ramanujan.Part1Ch8.Entry17Loggammaintegral.ramanujan_part1_ch8_entry17_loggammaintegral x n hx hn

-- created on 2026-10-10
