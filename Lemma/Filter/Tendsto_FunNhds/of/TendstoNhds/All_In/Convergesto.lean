import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_9_3.Part2
open Chapter9
open Chapter9.Convergesto


/--
[Convergesto.comp](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_3.lean)
-/
@[path]
private lemma main
  {E:Set ℝ}
  {f: ℝ → ℝ}
  {L x₀ : ℝ}
  {a:ℕ → ℝ}
-- given
  (hf: Convergesto E f L x₀)
  (ha: ∀ n:ℕ, a n ∈ E)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
-- imply
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) :=
-- proof
  Chapter9.Convergesto.comp hf ha hconv


-- created on 2026-10-22
