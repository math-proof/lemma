import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10Example1SqrtPoissonAsymptotic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10Example1SqrtPoissonAsymptotic


/--
[ramanujan_part1_ch3_entry10_example1_sqrt_poisson_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example1SqrtPoissonAsymptotic.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_example1_sqrt_poisson_asymptotic_eq
  :
-- imply
  (fun x : ℝ =>
    Real.log (∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
    (↑(Nat.factorial (j + 1)) : ℝ)) - (x + (1 / 2 : ℝ) * Real.log x - 1 / (8 * x) - 1 /
    (16 * x ^ 2))) =O[Filter.atTop] (fun x : ℝ =>
    1 / x ^ 3) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example1SqrtPoissonAsymptotic.ramanujan_part1_ch3_entry10_example1_sqrt_poisson_asymptotic


-- created on 2026-10-20
