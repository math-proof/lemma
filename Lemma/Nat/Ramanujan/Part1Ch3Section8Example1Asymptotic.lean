import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Section8Example1Asymptotic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Section8Example1Asymptotic


/--
[ramanujan_part1_ch3_section8_example1_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example1Asymptotic.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_section8_example1_asymptotic_eq
  {a : ℕ → ℂ}
  {ψ : ℂ → ℂ}
  {lam : WithBot ℝ}
  {eps : ℝ}
-- given
  (heps_pos : 0 < eps)
  (heps_lt_pi_div_two : lam ≠ (⊥ : WithBot ℝ) → eps < Real.pi / 2)
  (heps_lt_pi_div_two_bot : lam = (⊥ : WithBot ℝ) → eps < Real.pi / 2)
  (hsum : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) → lam < (↑z.re : WithBot ℝ) → HasSum (fun j : ℕ => (-1 : ℂ) ^ j * a j / ∏ k ∈ Finset.range (j + 1), (z + ((k + 1 : ℕ) : ℂ))) (ψ z)) :
-- imply
  ∀ N : ℕ, ∃ C : ℝ, ∃ R : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) →
    lam < (↑z.re : WithBot ℝ) →
    ((lam = (⊥ : WithBot ℝ) → |Complex.arg z| ≤ Real.pi / 2 - eps) ∧
    (∀ r : ℝ, lam = (↑r : WithBot ℝ) → |Complex.arg (z - (r : ℂ))| ≤ Real.pi /
    2 - eps)) →
    R ≤ ‖z‖ → ‖ψ z - ∑ j ∈ Finset.range (N + 1),
    ((-1 : ℂ) ^ j *
    (∑ k ∈ Finset.range (j + 1), a k *
    ((Nat.stirlingSecond (j + 1) (k + 1) : ℕ) : ℂ)) / z ^ (j + 1))‖ ≤ C /
    ‖z‖ ^ (N + 2) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example1Asymptotic.ramanujan_part1_ch3_section8_example1_asymptotic a ψ lam eps heps_pos heps_lt_pi_div_two heps_lt_pi_div_two_bot hsum


-- created on 2026-10-20
