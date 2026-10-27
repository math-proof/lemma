import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Filter
open Chapter8.Filter.Tendsto


/--
[Filter.Tendsto.int_natCast_atTop](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {R:Type}
  {f: ℤ → R}
  {l: Filter R} :
-- imply
  atTop.Tendsto f l ↔ atTop.Tendsto (f ∘ Nat.cast) l :=
-- proof
  Chapter8.Filter.Tendsto.int_natCast_atTop f l


-- created on 2026-10-22
