import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Section8Example4Integrable


/--
[f_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
private lemma f_neg_one_eq
  {x : ℂ}
-- given
  (h : (-1 : ℤ) ≤ -1) :
-- imply
  f ⟨-1, h⟩ x = 1 := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable.f_neg_one h x

/--
[f_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
private lemma f_natCast_eq
  {k : ℕ}
  {x : ℂ}
-- given
  (h : (-1 : ℤ) ≤ k) :
-- imply
  f ⟨k, h⟩ x = generalizedBellGenerating 0 1 x k := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable.f_natCast k h x

/--
[ramanujan_part1_ch3_section8_example4_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_section8_example4_integrable_eq
  {m : ℕ}
  {x : ℂ} :
-- imply
  IntervalIntegrable (fun t : ℝ => x * f ⟨(m : ℤ) - 1,
    by omega⟩ ((t : ℂ) * x)) MeasureTheory.volume 0 1 := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable.ramanujan_part1_ch3_section8_example4_integrable m x


-- created on 2026-10-20
