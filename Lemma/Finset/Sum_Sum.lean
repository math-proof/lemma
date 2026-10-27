import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_7_1
open Finset


/--
[finite_series_comm](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {X: Finset XX}
  {Y: Finset YY}
  {f: XX × YY → ℝ} :
-- imply
  ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) :=
-- proof
  Finset.finite_series_comm X Y f


-- created on 2026-10-20
