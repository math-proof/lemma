import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_2
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Filter
open Chapter8.Filter.Eventually


/--
[Filter.Eventually.int_natCast_atTop](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
-- given
  (p: ℤ → Prop) :
-- imply
  (∀ᶠ n in .atTop, p n) ↔ ∀ᶠ n:ℕ in .atTop, p ↑n :=
-- proof
  Chapter8.Filter.Eventually.int_natCast_atTop p


-- created on 2026-10-22
