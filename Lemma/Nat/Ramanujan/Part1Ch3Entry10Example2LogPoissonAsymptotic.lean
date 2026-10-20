import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10Example2LogPoissonAsymptotic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10Example2LogPoissonAsymptotic


/--
[ramanujan_part1_ch3_entry10_example2_log_poisson_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example2LogPoissonAsymptotic.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_example2_log_poisson_asymptotic_eq
  :
-- imply
  ∃ (C : ℝ) (x₀ : ℝ), 0 < C ∧ ∀ (x : ℝ), x₀ ≤ x → ∃ (S : ℝ),
    HasSum (fun j : ℕ => x ^ (j + 1) * Real.log ((j + 2 : ℝ)) / (Nat.factorial (j + 1) : ℝ)) S ∧
    |Real.exp (-x) * S - Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2)| ≤ C / x ^ 3 := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example2LogPoissonAsymptotic.ramanujan_part1_ch3_entry10_example2_log_poisson_asymptotic


-- created on 2026-10-20
