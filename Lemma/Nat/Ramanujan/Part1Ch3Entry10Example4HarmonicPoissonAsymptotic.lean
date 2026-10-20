import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10Example4HarmonicPoissonAsymptotic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10Example4HarmonicPoissonAsymptotic


/--
[ramanujan_part1_ch3_entry10_example4_harmonic_poisson_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example4HarmonicPoissonAsymptotic.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_example4_harmonic_poisson_asymptotic_eq
  :
-- imply
  Asymptotics.IsBigO Filter.atTop (fun x : ℝ => Real.exp (-x) *
    (∑' (k : ℕ),
    (x ^ k * (∑ j ∈ Finset.Icc 1 k, (1 : ℝ) / (j : ℝ)) /
    (k.factorial : ℝ))) - (Real.log x + Real.eulerMascheroniConstant)) (fun x : ℝ =>
    (1 : ℝ) / x) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example4HarmonicPoissonAsymptotic.ramanujan_part1_ch3_entry10_example4_harmonic_poisson_asymptotic


-- created on 2026-10-20
