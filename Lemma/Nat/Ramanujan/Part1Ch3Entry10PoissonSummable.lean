import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10PoissonSummable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10PoissonSummable


/--
[ramanujan_part1_ch3_entry10_poisson_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10PoissonSummable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_poisson_summable_eq
  {φ : ℝ → ℂ}
  {F : Finset ℕ}
-- given
  (hφ : ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ᶠ (x : ℝ) in Filter.atTop, ‖φ x‖ ≤ C * x ^ p) :
-- imply
  ∀ᶠ (x : ℝ) in Filter.atTop,
    Summable (fun j : ℕ => if j ∈ F then 0 else ((x : ℂ) ^ j * φ (j : ℝ) / (Nat.factorial j : ℂ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10PoissonSummable.ramanujan_part1_ch3_entry10_poisson_summable φ F hφ


-- created on 2026-10-20
