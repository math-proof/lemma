import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry11CorollaryNewtonGirard
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry11CorollaryNewtonGirard


/--
[ramanujan_part1_ch3_entry11_corollary_newton_girard_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry11CorollaryNewtonGirard.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry11_corollary_newton_girard_general_eq
  {a e p : ℕ → ℂ}
-- given
  (he : ∀ n : ℕ, HasSum (fun s : { s : Finset ℕ // s.card = n } => ∏ j ∈ (s : Finset ℕ), a j) (e n))
  (hp : ∀ k : ℕ, 1 ≤ k → HasSum (fun j : ℕ => (a j) ^ k) (p k)) :
-- imply
  ∀ n : ℕ, (n : ℂ) * e n = ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (k - 1) * p k * e (n - k) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry11CorollaryNewtonGirard.ramanujan_part1_ch3_entry11_corollary_newton_girard_general a e p he hp

/--
[ramanujan_part1_ch3_entry11_corollary_newton_girard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry11CorollaryNewtonGirard.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry11_corollary_newton_girard_eq
  {a e p : ℕ → ℂ}
-- given
  (ha : Summable (fun j : ℕ => ‖a j‖))
  (he : ∀ n : ℕ, HasSum (fun s : { s : Finset ℕ // s.card = n } => ∏ j ∈ (s : Finset ℕ), a j) (e n))
  (hp : ∀ k : ℕ, 1 ≤ k → HasSum (fun j : ℕ => (a j) ^ k) (p k)) :
-- imply
  ∀ n : ℕ, 1 ≤ n → (n : ℂ) * e n = ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (k - 1) * p k * e (n - k) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry11CorollaryNewtonGirard.ramanujan_part1_ch3_entry11_corollary_newton_girard a e p ha he hp


-- created on 2026-10-20
