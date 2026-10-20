import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10PoissonAsymptotic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10PoissonAsymptotic


/--
[twoAssocStirlingSecond_eq_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10PoissonAsymptotic.lean)
-/
@[path]
private lemma twoAssocStirlingSecond_eq_canonical_eq
  {n k : ℕ} :
-- imply
  twoAssocStirlingSecond n k = MetaMathlibExt.twoAssocStirlingSecond n k := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10PoissonAsymptotic.twoAssocStirlingSecond_eq_canonical n k

/--
[ramanujan_part1_ch3_entry10_poisson_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10PoissonAsymptotic.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_poisson_asymptotic_eq
  {M : ℕ}
  {φ : ℝ → ℂ}
  {G : ℝ → ℝ}
  {A : ℝ}
  {F : Finset ℕ}
-- given
  (hM : 0 < M)
  (hA : 1 ≤ A)
  (h_poly : ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ᶠ x in Filter.atTop, ‖φ x‖ ≤ C * x ^ p ∧ ‖G x‖ ≤ C * x ^ p)
  (hG_ge : ∀ᶠ x in Filter.atTop, (1 : ℝ) ≤ G x)
  (h_deriv : ∀ m : ℕ, 0 < m → ∀ᶠ x in Filter.atTop, (∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (iteratedDeriv (k - 1) φ) x) ∧ ‖iteratedDeriv m φ x / (Nat.factorial m : ℂ)‖ ≤ G x * (A / x) ^ m) :
-- imply
  Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ =>
    ((Real.exp (-x) : ℂ)) *
    (∑' j : ℕ, if j ∈ F then (0 : ℂ) else
    (((x ^ j / (Nat.factorial j : ℝ) : ℝ) : ℂ) * φ (j : ℝ)))
    - φ x
    - ∑ k ∈ Finset.Icc 2 M, ∑ n ∈ Finset.Icc k (2 * k - 2),
    (((twoAssocStirlingSecond n (n + 1 - k) : ℤ) : ℂ) * ((x : ℂ) ^ (n - k + 1)) *
    (iteratedDeriv n φ x / (Nat.factorial n : ℂ))))
    (fun x : ℝ => G x / (x : ℝ) ^ M) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10PoissonAsymptotic.ramanujan_part1_ch3_entry10_poisson_asymptotic M hM φ G A hA F h_poly hG_ge h_deriv


-- created on 2026-10-20
