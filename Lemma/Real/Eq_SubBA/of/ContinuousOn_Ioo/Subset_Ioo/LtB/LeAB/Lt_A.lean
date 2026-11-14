import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[α_length_of_cts](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {α:ℝ → ℝ}
  {I: BoundedInterval}
  {a b: ℝ}
-- given
  (haa: a < I.a)
  (hab: I.a ≤ I.b)
  (hbb: I.b < b)
  (hI : I ⊆ Ioo a b)
  (hα: ContinuousOn α (Ioo a b)) :
-- imply
  α[I]ₗ = α I.b - α I.a :=
-- proof
  Chapter11.α_length_of_cts haa hab hbb hI hα


-- created on 2026-10-22
