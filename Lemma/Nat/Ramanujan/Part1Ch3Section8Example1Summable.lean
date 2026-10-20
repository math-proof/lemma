import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Section8Example1Summable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Section8Example1Summable


/--
[ramanujan_part1_ch3_section8_example1_summable_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example1Summable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_section8_example1_summable_general_eq
  {a : ℕ → ℂ}
  {lam : Option ℝ}
  {eps : ℝ}
-- given
  (heps_pos : 0 < eps)
  (hSumm : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) → (∀ l : ℝ, lam = some l → l < z.re) → Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) / ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ)))) :
-- imply
  ∃ R : ℝ, ∀ z : ℂ, sector lam eps z → R < ‖z‖ →
    Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
    ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example1Summable.ramanujan_part1_ch3_section8_example1_summable_general a lam eps heps_pos hSumm

/--
[ramanujan_part1_ch3_section8_example1_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example1Summable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_section8_example1_summable_eq
  {a : ℕ → ℂ}
  {lam : Option ℝ}
  {eps : ℝ}
-- given
  (heps_pos : 0 < eps)
  (heps_lt : match lam with | some _ => eps < Real.pi / 2 | none => eps < Real.pi)
  (hSumm : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) → (∀ l : ℝ, lam = some l → l < z.re) → Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) / ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ)))) :
-- imply
  ∃ R : ℝ, ∀ z : ℂ, sector lam eps z → R < ‖z‖ →
    Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
    ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example1Summable.ramanujan_part1_ch3_section8_example1_summable a lam eps heps_pos heps_lt hSumm


-- created on 2026-10-20
