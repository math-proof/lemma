import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch8Entry8Digammaseries
open scoped Nat Real BigOperators Interval
open Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch8
open Entry8Digammaseries


/--
[chapter8Digamma_eq_Complex_digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma chapter8Digamma_eq_Complex_digamma_eq
  {z : ℂ} :
-- imply
  chapter8Digamma z = Complex.digamma z := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries.chapter8Digamma_eq_Complex_digamma z

/--
[ramanujan_part1_ch8_entry8_digammaseries_complex_digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry8_digammaseries_complex_digamma_eq
  {a b : ℂ}
-- given
  (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) :
-- imply
  HasSum (chapter8Entry8Term a b)
    ((Complex.digamma ((a + 2 * b) / (2 * b)) -
    Complex.digamma ((a + b) / (2 * b))) /
    (2 * b))
    (SummationFilter.conditional ℕ) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries.ramanujan_part1_ch8_entry8_digammaseries_complex_digamma a b hb hdenom

/--
[ramanujan_part1_ch8_entry8_digammaseries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry8_digammaseries_eq
  {a b : ℂ}
-- given
  (hb : b ≠ 0)
  (hleft : Complex.Gamma ((a + 2 * b) / (2 * b)) ≠ 0)
  (hright : Complex.Gamma ((a + b) / (2 * b)) ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) :
-- imply
  HasSum (chapter8Entry8Term a b)
    ((chapter8Digamma ((a + 2 * b) / (2 * b)) -
    chapter8Digamma ((a + b) / (2 * b))) /
    (2 * b))
    (SummationFilter.conditional ℕ) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries.ramanujan_part1_ch8_entry8_digammaseries a b hb hleft hright hdenom


-- created on 2026-10-20
