import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_9_4.Part2
open Chapter9
open Filter
open Filter.Tendsto


/--
[_root_.Filter.Tendsto.comp_of_continuous](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_4.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f: ℝ → ℝ}
  {x₀:ℝ}
  {a: ℕ → ℝ}
-- given
  (h_cont: ContinuousWithinAt f X x₀)
  (ha: ∀ n, a n ∈ X)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
-- imply
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)) :=
-- proof
  Filter.Tendsto.comp_of_continuous h_cont ha hconv


-- created on 2026-10-22
