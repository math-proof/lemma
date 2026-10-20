import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Section8Example4BernoulliIntegral
open Section8Example4Integrable (f f_natCast)
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Section8Example4BernoulliIntegral


/--
[ramanujan_part1_ch3_section8_example4_bernoulli_integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4BernoulliIntegral.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_section8_example4_bernoulli_integral_eq
  {m : ℕ}
  {x : ℂ} :
-- imply
  ∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), x * f ⟨(↑m : ℤ) - 1, by omega⟩ ((↑t : ℂ) * x) =
    ∑ k ∈ Finset.range (m + 1), (↑(Nat.choose m k) : ℂ) * (↑(bernoulli (m - k)) : ℂ) *
    f ⟨↑k, by omega⟩ x / (↑(k + 1) : ℂ) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4BernoulliIntegral.ramanujan_part1_ch3_section8_example4_bernoulli_integral m x


-- created on 2026-10-20
